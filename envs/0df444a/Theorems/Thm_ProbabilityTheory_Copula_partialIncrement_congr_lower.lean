-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_congr_lower
-- name    : ProbabilityTheory.Copula.partialIncrement_congr_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:36.608102+00:00
-- url     : https://prove2.me/theorems/6a2f30f5-69d6-4b8e-bcb1-f0f4bc7abd1c
-- title:
--   Copula: partial Increment congr lower
-- statement:
--   The Copula construction uses the partial Increment congr lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L26-L34
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L26-L34

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

theorem ProbabilityTheory.Copula.partialIncrement_congr_lower (a a' b : Fin d → I) (s : Finset (Fin d))
    (ha : ∀ i ∈ s, a i = a' i) : partialIncrement F a b s = partialIncrement F a' b s := by sorry
