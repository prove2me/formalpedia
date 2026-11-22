-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_abs_sub_le_sum_abs
-- name    : ProbabilityTheory.Copula.IsClassical.abs_sub_le_sum_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:47.2207+00:00
-- url     : https://prove2.me/theorems/da70f72d-24a1-4ac1-a7f0-b97067bbc348
-- title:
--   Is Classical: abs sub le sum abs
-- statement:
--   The sharp Lipschitz estimate in the sum of coordinate distances.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L173-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L173-L180

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}

theorem ProbabilityTheory.Copula.IsClassical.abs_sub_le_sum_abs (hF : IsClassical F) (a b : Fin d → I) :
    |F a - F b| ≤ ∑ i, |(a i : ℝ) - (b i : ℝ)| := by sorry
