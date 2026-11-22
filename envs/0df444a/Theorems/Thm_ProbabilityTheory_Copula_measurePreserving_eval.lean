-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_measurePreserving_eval
-- name    : ProbabilityTheory.Copula.measurePreserving_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:56.996187+00:00
-- url     : https://prove2.me/theorems/019d4d4e-381d-4afe-9155-4a16a8b7ec2a
-- title:
--   Copula: measure Preserving eval
-- statement:
--   Coordinate projections preserve the uniform measure.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L62-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Basic.lean#L62-L64

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory
open ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.measurePreserving_eval (C : Copula d) (i : Fin d) :
    MeasurePreserving (fun x => x i) C.toMeasure volume := by sorry
