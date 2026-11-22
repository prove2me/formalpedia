-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_measureReal_rectangle_two
-- name    : ProbabilityTheory.Copula.measureReal_rectangle_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:15.703732+00:00
-- url     : https://prove2.me/theorems/d6bd7b26-0362-40cf-8eb5-202d6a8b163d
-- title:
--   Copula: measure Real rectangle two
-- statement:
--   Bivariate rectangle probabilities written as four CDF evaluations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L151-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L151-L154

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

theorem ProbabilityTheory.Copula.measureReal_rectangle_two (C : Copula 2) (a b : Fin 2 → I) (hab : a ≤ b) :
    C.toMeasure.real (Set.pi univ (fun i => Ioc (a i) (b i))) =
      C.cdf b - C.cdf ![a 0, b 1] - C.cdf ![b 0, a 1] + C.cdf a := by sorry
