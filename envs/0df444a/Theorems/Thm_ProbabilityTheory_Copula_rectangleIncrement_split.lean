-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_split
-- name    : ProbabilityTheory.Copula.rectangleIncrement_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:45.018266+00:00
-- url     : https://prove2.me/theorems/ad5b44cf-4b79-4ff9-8c1f-21c78a41a41e
-- title:
--   Copula: rectangle Increment split
-- statement:
--   Finite additivity under a cut, including cuts at the endpoints.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L37-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L37-L51

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

theorem ProbabilityTheory.Copula.rectangleIncrement_split (a b : Fin d → I) (i : Fin d) (t : I) :
    rectangleIncrement F a b =
      rectangleIncrement F a (Function.update b i t) +
        rectangleIncrement F (Function.update a i t) b := by sorry
