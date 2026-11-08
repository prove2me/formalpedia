-- Prove2me | Theorems.Thm_UniversalSubmod_concavity_segment
-- name    : UniversalSubmod.concavity_segment
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:51:39.501118+00:00
-- url     : https://prove2.me/theorems/446d0ed2-50eb-459b-9dac-ec651b873026
-- title:
--   Concavity display, §4, p.10 — $\partial_v\partial_vF\le0$ for $v\ge0$; $F$ is concave on segments between $x\le y$
-- statement:
--   Let $f:2^{[n]}\to\mathbb R_{\ge0}$ be nonnegative submodular with multilinear extension $F$. Then:
--
--   1. for any $x\in[0,1]^n$ and $v\in\mathbb R^n_{\ge0}$,
--   $$
--   \partial_v\partial_vF(x)=\sum_{i,j=1}^n v_iv_j\,\partial_i\partial_jF(x)\le0;
--   $$
--   2. $F$ is concave on any line segment connecting points $x,y\in[0,1]^n$ with $x_i\le y_i$ for all $i\in[n]$, that is, $t\mapsto F(x+t(y-x))$ is concave on $[0,1]$.
--
--   Concavity along nonnegative directions is the tool behind Lemmas 2.1 and 2.2: it compares the value of $F$ at a point with its values at the endpoints of a monotone segment.
--
--   **Formalization Note** Directional second derivatives are iterated Fréchet derivatives of the published (polynomial) $F$.
--
--   Differences from the source:
--   - encoding: $\partial_v\partial_vF(x)$ → `fderiv ℝ (fun y => fderiv ℝ (F f) y v) x v`; reason: $F$ is a polynomial, so this is the classical second directional derivative
--   - encoding: concave on the segment connecting $x$ and $y$ → `ConcaveOn ℝ (Set.Icc 0 1) (fun t => F f (x + t • (y - x)))`; reason: the segment parametrized by $t\in[0,1]$
--   - encoding: the ground set $[n]$, subsets $S\subseteq[n]$, $f:2^{[n]}\to\mathbb R_{\ge0}$ → `Fin n`, `Finset (Fin n)`, a real-valued `f` with $f(S)\ge0$ for all $S$; reason: a relabelling of $[n]$; the same functions
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), §4, display at the top of p.10

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

/-- **Concavity along monotone segments** (Adamczyk, Ueltzen, Vondrák, *Optimal universal sets for
submodular functions*, manuscript of November 3, 2026, §4, display at the top of p.10). Let `F` be
the multilinear extension of a nonnegative submodular `f : 2^[n] → ℝ≥0`. For any `x ∈ [0,1]^n` and
`v ∈ ℝ^n_{≥0}`, `∂_v∂_vF(x) = ∑_{i,j} vᵢvⱼ ∂ᵢ∂ⱼF(x) ≤ 0`. This means that `F` is concave on any line
segment connecting points `x, y ∈ [0,1]^n` with `xᵢ ≤ yᵢ` for all `i`.

**Formalization Note.** `F` is the published `NonmonotoneSubmod.Shared.F` (a polynomial, everywhere
differentiable). Directional second derivatives are iterated Fréchet derivatives. The segment
from `x` to `y` is parametrized as `t ↦ x + t(y − x)`, `t ∈ [0,1]`. -/
theorem concavity_segment {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) :
    (∀ x v : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, 0 ≤ v i) →
      fderiv ℝ (fun y => fderiv ℝ (F f) y v) x v =
        ∑ i, ∑ j, v i * v j *
          fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x (Pi.single i (1 : ℝ)) ∧
      fderiv ℝ (fun y => fderiv ℝ (F f) y v) x v ≤ 0) ∧
    (∀ x y : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, x i ≤ y i) →
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => F f (x + t • (y - x)))) := by sorry

end UniversalSubmod
