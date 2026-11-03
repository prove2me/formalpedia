-- Prove2me | Theorems.Thm_ProxFlatIP_lemma_7
-- name    : ProxFlatIP.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:37.132096+00:00
-- url     : https://prove2.me/theorems/1a0f8107-6063-42d6-8ddd-3fac4e1c0271
-- title:
--   Lemma 7 (corrected: $0\in P$) — $\kappa_d(\alpha)\le\sum_i\kappa_{d_i}(\alpha)$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have full column rank, $b\in\mathbb Z^m$, and $P=P(A,b)$. Let $\alpha\in\mathbb Z^n$ be nonzero, suppose $0\in P$ and that $\max\{\alpha^\top x:x\in P\}$ is attained, and let $\dim P=:d=\sum_{i=0}^kd_i$, where each $d_i$ is a positive integer. Then
--   $$\kappa_d(\alpha)\le\sum_{i=0}^k\kappa_{d_i}(\alpha).$$
--
--   This lifts low-dimensional bounds to high dimension: it splits $\kappa_d$ along a path of faces of dimensions $d_0,\dots,d_k$.
--
--   Differences from the source:
--   - correction: no hypothesis on the origin beyond the standing P ∩ Zⁿ ≠ ∅ → 0 ∈ P; reason: the printed statement is false: for A = (I ; −I), b = (6,6,−5,−5), P = [5,6]², α = e₁, d = 2 = 1 + 1, κ₂(α) = 6 while no I has dim P_I = 1; the proof's path of points ends at x*_t := 0 and uses S(x*) ⊆ P, which needs 0 ∈ P; every use of the lemma (p.10) has P ∩ Zⁿ = {0}, hence 0 ∈ P
--   - encoding: κ_d(α) defined through maxima of α⊤x over slices of P → hypothesis that max{α⊤x : x ∈ P} is attained; reason: definition (2) and the proof's first step ("let x* maximize α⊤x over P") presuppose the maximum; it excludes only instances where the source's κ has no value
--   - encoding: κ_{d_i} is a maximum over the I with dim P_I = d_i, with no value when there is no such I → sSup, with value 0 on an empty family; reason: no instance with a nonempty family changes; for an empty family the source has no value
--   - encoding: κ_I is the number with max_{x∈P_I} α⊤x = κ_I·Δ^α_I(A), with no value when Δ^α_I(A) = 0 → κ_I = 0 there (Lean's x/0 = 0); reason: Δ^α_I(A) = 0 only when α lies in the row space of A_I, so α⊤x = 0 on P_I and (2) holds for every κ_I; no instance with Δ^α_I(A) > 0 changes
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Lemma 7, p.9

import Mathlib
import Definitions.Def_ProxFlatIP_Kappa

open Matrix

namespace ProxFlatIP

/-- **Lemma 7** (corrected: `0 ∈ P`) (arXiv:2211.14941v1, Lemma 7, p.9). Let `α ∈ ℤⁿ` be nonzero,
`0 ∈ P`, `max{α⊤x : x ∈ P}` attained, and `dim P = d = ∑_{i=0}^k d_i` with each `d_i` a positive
integer. Then `κ_d(α) ≤ ∑_{i=0}^k κ_{d_i}(α)`.

**Formalization Note.** The hypothesis `0 ∈ P` is not printed. Without it the statement is false: for
`A = (I ; −I)`, `b = (6, 6, −5, −5)`, so that `P = [5,6]²`, and `α = e₁`, `d = 1 + 1`, one has `κ₂ = 6`
and no index set with `dim P_I = 1`. The proof uses it: its sequence of points ends at `x*_t := 0`,
and `S(x*) ⊆ P` needs `0 ∈ P`. Every use of the lemma (p.10) has `P ∩ ℤⁿ = {0}`, so `0 ∈ P` and `P`
is bounded. The attained maximum is what the proof's first step ("let `x*` maximize `α⊤x` over `P`")
and the definition (2) of `κ_I` presuppose; it rules out the junk value `sSup` takes on an unbounded
set. `κ` uses the conventions of `kappaD` (`sSup ∅ = 0`, `x / 0 = 0`). -/
theorem lemma_7 {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (b : Fin m → ℤ)
    (α : Fin n → ℤ) (hα : α ≠ 0) (h0 : (0 : Fin n → ℝ) ∈ Poly A b)
    (hmax : ∃ x ∈ Poly A b, ∀ y ∈ Poly A b, castVec α ⬝ᵥ y ≤ castVec α ⬝ᵥ x)
    (ds : Fin (k + 1) → ℕ) (hds : ∀ i, 0 < ds i) (hd : dimLin (Poly A b) = ∑ i, ds i) :
    kappaD A b α (dimLin (Poly A b)) ≤ ∑ i, kappaD A b α (ds i) := by sorry

end ProxFlatIP
