-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_cdf
-- name    : ProbabilityTheory.Copula.rectangleIncrement_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:47.388925+00:00
-- url     : https://prove2.me/theorems/913b174c-c2d0-4dcd-86fe-d62c4cdc036e
-- title:
--   Copula: rectangle Increment cdf
-- statement:
--   The alternating CDF sum equals the probability of the half-open rectangle.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L136-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L136-L142

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

theorem ProbabilityTheory.Copula.rectangleIncrement_cdf (C : Copula d) (a b : Fin d → I) (hab : a ≤ b) :
    rectangleIncrement C.cdf a b = C.toMeasure.real (Set.pi univ (fun i => Ioc (a i) (b i))) := by sorry
