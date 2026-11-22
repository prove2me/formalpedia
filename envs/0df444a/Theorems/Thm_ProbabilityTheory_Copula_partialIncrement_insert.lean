-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_insert
-- name    : ProbabilityTheory.Copula.partialIncrement_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:44.114058+00:00
-- url     : https://prove2.me/theorems/0efbcd62-76a3-40f3-ac24-16ccf3375484
-- title:
--   Copula: partial Increment insert
-- statement:
--   The Copula construction uses the partial Increment insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L52-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L52-L69

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Rectangle
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.partialIncrement_insert (F : (Fin d → I) → ℝ) (a b : Fin d → I)
    (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) :
    partialIncrement F a b (insert i s) =
      partialIncrement F a b s - partialIncrement F a (Function.update b i (a i)) s := by sorry
