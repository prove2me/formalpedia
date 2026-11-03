-- Prove2me | Theorems.Thm_ProxFlatIP_lemma_3
-- name    : ProxFlatIP.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:28.623201+00:00
-- url     : https://prove2.me/theorems/53ba972f-0bb9-42f4-8a7f-a2514db3bc74
-- title:
--   Lemma 3 — $\kappa_1(\alpha)<1$ and $\kappa_2(\alpha)<1$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have full column rank, $b\in\mathbb Z^m$, and $P=P(A,b)$. Let $\alpha\in\mathbb Z^n$ be nonzero, and suppose $P\cap\mathbb Z^n=\{0\}$. Then
--   $$\kappa_1(\alpha)<1\quad\text{and}\quad\kappa_2(\alpha)<1.$$
--
--   These are the base cases of the dimension lifting, in dimensions $1$ and $2$.
--
--   Differences from the source:
--   - encoding: κ_d is a maximum over the I with dim P_I = d, with no value when there is no such I → sSup, with value 0 on an empty family; reason: no instance with a nonempty family changes; for an empty family, for example κ₂ when n = 1, the source has no value
--   - encoding: κ_I is the number with max_{x∈P_I} α⊤x = κ_I·Δ^α_I(A), with no value when Δ^α_I(A) = 0 → κ_I = 0 there (Lean's x/0 = 0); reason: Δ^α_I(A) = 0 only when α lies in the row space of A_I, so α⊤x = 0 on P_I and (2) holds for every κ_I; no instance with Δ^α_I(A) > 0 changes
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Lemma 3, p.7

import Mathlib
import Definitions.Def_ProxFlatIP_Kappa

open Matrix

namespace ProxFlatIP

/-- **Lemma 3** (arXiv:2211.14941v1, Lemma 3, p.7). Let `α ∈ ℤⁿ` be nonzero and `P ∩ ℤⁿ = {0}`.
Then `κ₁(α) < 1` and `κ₂(α) < 1`. -/
theorem lemma_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (b : Fin m → ℤ)
    (α : Fin n → ℤ) (hα : α ≠ 0) (hP : Poly A b ∩ {x | IsIntegralPt x} = {0}) :
    kappaD A b α 1 < 1 ∧ kappaD A b α 2 < 1 := by sorry

end ProxFlatIP
