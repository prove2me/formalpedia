-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_two
-- name    : ProbabilityTheory.Copula.rectangleIncrement_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:52.341203+00:00
-- url     : https://prove2.me/theorems/bf3bcea3-bef8-482e-82c3-60e43fba092f
-- title:
--   Copula: rectangle Increment two
-- statement:
--   The familiar four-term increment in dimension two.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L78-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L78-L90

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

theorem ProbabilityTheory.Copula.rectangleIncrement_two (F : (Fin 2 → I) → ℝ) (a b : Fin 2 → I) :
    rectangleIncrement F a b = F b - F ![a 0, b 1] - F ![b 0, a 1] + F a := by sorry
