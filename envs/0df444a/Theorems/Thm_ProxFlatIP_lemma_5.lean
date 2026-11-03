-- Prove2me | Theorems.Thm_ProxFlatIP_lemma_5
-- name    : ProxFlatIP.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:34.957942+00:00
-- url     : https://prove2.me/theorems/0acbdb62-7a2c-4f0d-9aaf-588d2c2fc42c
-- title:
--   Lemma 5 — $\kappa_3(\alpha)<4/3$
-- statement:
--   Let $A\in\mathbb Z^{m\times3}$ have full column rank, $b\in\mathbb Z^m$, and $P=P(A,b)$. Let $\alpha\in\mathbb Z^3$ be nonzero, and suppose $P\cap\mathbb Z^3=\{0\}$. Then
--   $$\kappa_3(\alpha)<\frac43.$$
--
--   This is the three-dimensional base case. With Lemma 3 it gives the bound $\kappa_d<(4d+2)/9$ in every dimension.
--
--   Differences from the source:
--   - encoding: κ₃ is a maximum over the I with dim P_I = 3, with no value when there is no such I → sSup, with value 0 on an empty family; reason: no instance with a nonempty family changes; when dim P < 3 the source has no value
--   - encoding: κ_I is the number with max_{x∈P_I} α⊤x = κ_I·Δ^α_I(A), with no value when Δ^α_I(A) = 0 → κ_I = 0 there (Lean's x/0 = 0); reason: Δ^α_I(A) = 0 only when α lies in the row space of A_I, so α⊤x = 0 on P_I and (2) holds for every κ_I; no instance with Δ^α_I(A) > 0 changes
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Lemma 5, p.8

import Mathlib
import Definitions.Def_ProxFlatIP_Kappa

open Matrix

namespace ProxFlatIP

/-- **Lemma 5** (arXiv:2211.14941v1, Lemma 5, p.8). For `A ∈ ℤ^{m×3}` of full column rank, `b ∈ ℤᵐ`
and nonzero `α ∈ ℤ³` with `P ∩ ℤ³ = {0}`, one has `κ₃(α) < 4/3`. -/
theorem lemma_5 {m : ℕ} (A : Matrix (Fin m) (Fin 3) ℤ) (hA : FullColRank A) (b : Fin m → ℤ)
    (α : Fin 3 → ℤ) (hα : α ≠ 0) (hP : Poly A b ∩ {x | IsIntegralPt x} = {0}) :
    kappaD A b α 3 < 4 / 3 := by sorry

end ProxFlatIP
