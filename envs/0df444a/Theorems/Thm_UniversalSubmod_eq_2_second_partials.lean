-- Prove2me | Theorems.Thm_UniversalSubmod_eq_2_second_partials
-- name    : UniversalSubmod.eq_2_second_partials
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:51:42.405394+00:00
-- url     : https://prove2.me/theorems/12532feb-fe9a-408e-97be-3b2a8955a7f9
-- title:
--   Equation (2), p.9 — $\partial_i\partial_jF$ as an expectation, $\partial_i\partial_jF\le0$ and $|\partial_i\partial_jF|\le 2\max f$
-- statement:
--   Let $f:2^{[n]}\to\mathbb R_{\ge0}$ be nonnegative submodular with multilinear extension $F(x)=\sum_{S\subseteq[n]}f(S)\prod_{i\in S}x_i\prod_{i\notin S}(1-x_i)$. For $x\in[0,1]^n$ and $i,j\in[n]$:
--
--   1. if $i\ne j$, then
--   $$
--   \partial_i\partial_jF(x)=\mathbb E\big[f(A\cup\{i,j\})-f(A\cup\{i\})-f(A\cup\{j\})+f(A)\big],
--   $$
--   where $A\subseteq[n]\setminus\{i,j\}$ contains each $l\in[n]\setminus\{i,j\}$ independently with probability $x_l$;
--   2. if $i=j$, then $\partial_i\partial_jF(x)=0$;
--   3. (Equation (2)) $\partial_i\partial_jF(x)\le0$ and $|\partial_i\partial_jF(x)|\le 2\max_{S\subseteq[n]}f(S)$.
--
--   The sign of the mixed partials is the analytic form of submodularity; it drives the concavity of $F$ along nonnegative directions and the Gaussian interpolation in the proof of Theorem 2.3.
--
--   **Formalization Note** $F$ is the published multilinear extension, a polynomial on all of $\mathbb R^n$, so it is everywhere differentiable and $\partial_i\partial_jF(x)$ is the iterated Fréchet derivative $\partial_i(\partial_jF)(x)$ along the coordinate vectors; no junk value arises.
--
--   Differences from the source:
--   - encoding: $\partial_i\partial_jF(x)$ → `fderiv ℝ (fun y => fderiv ℝ (F f) y (e_j)) x (e_i)`; reason: $F$ is a polynomial, so this is the classical mixed partial
--   - encoding: the expectation over the random set $A$ → the explicit sum over $A\subseteq[n]\setminus\{i,j\}$ with weights $\prod_{l}(x_l$ or $1-x_l)$; reason: the definition of that expectation
--   - encoding: $\|\partial_i\partial_jF\|_\infty\le 2\max f$ on $[0,1]^n$ → $|\partial_i\partial_jF(x)|\le 2\,\mathrm{OPT}(f)$ for every $x\in[0,1]^n$; reason: a supremum bound is the same as the pointwise bound
--   - encoding: the ground set $[n]$, subsets $S\subseteq[n]$, $f:2^{[n]}\to\mathbb R_{\ge0}$ → `Fin n`, `Finset (Fin n)`, a real-valued `f` with $f(S)\ge0$ for all $S$; reason: a relabelling of $[n]$; the same functions
--   - encoding: $\max_{S\subseteq[n]} f(S)$ → the published `OPT f` (a maximum over the nonempty finite family of all subsets); reason: the same number
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), §4, display before Equation (2) and Equation (2), p.9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

/-- **Equation (2)** and the display before it (second partial derivatives of the multilinear
extension; Adamczyk, Ueltzen, Vondrák, *Optimal universal sets for submodular functions*,
manuscript of November 3, 2026, §4, p.9). Let `f : 2^[n] → ℝ≥0` be nonnegative submodular with
multilinear extension `F`. For `x ∈ [0,1]^n` and `i, j ∈ [n]`,
`∂ᵢ∂ⱼF(x) = E[f(A ∪ {i,j}) − f(A ∪ {i}) − f(A ∪ {j}) + f(A)]` if `i ≠ j` and `0` if `i = j`,
the expectation over `A ⊆ [n] ∖ {i,j}` containing each `l` independently with probability `x_l`;
and (2): `∂ᵢ∂ⱼF ≤ 0` and `‖∂ᵢ∂ⱼF‖_∞ ≤ 2 max_{S⊆[n]} f(S)`.

**Formalization Note.** `F` is the published `NonmonotoneSubmod.Shared.F`, a polynomial on all of
`ℝ^n`, hence everywhere differentiable: `∂ᵢ∂ⱼF(x)` is the iterated Fréchet derivative
`∂ᵢ(∂ⱼF)(x)` along the coordinate vectors, and no junk value of `fderiv` arises. The expectation
over `A` is the explicit finite sum with the product weights. The sup-norm bound is stated
pointwise on `[0,1]^n`. -/
theorem eq_2_second_partials {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (i j : Fin n) :
    let d2 : ℝ := fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x (Pi.single i (1 : ℝ))
    (i ≠ j → d2 = ∑ A ∈ (Finset.univ \ {i, j}).powerset,
        (∏ l ∈ Finset.univ \ {i, j}, if l ∈ A then x l else 1 - x l) *
          (f (A ∪ {i, j}) - f (A ∪ {i}) - f (A ∪ {j}) + f A)) ∧
    (i = j → d2 = 0) ∧ d2 ≤ 0 ∧ |d2| ≤ 2 * OPT f := by sorry

end UniversalSubmod
