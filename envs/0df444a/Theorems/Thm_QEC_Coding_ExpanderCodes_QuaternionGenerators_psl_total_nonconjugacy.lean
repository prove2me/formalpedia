-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_psl_total_nonconjugacy
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.psl_total_nonconjugacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:40:43.225895+00:00
-- url     : https://prove2.me/theorems/2ef76c1d-dd69-4b2f-9d55-13c97ff245c5
-- title:
--   Quaternion Generators: psl total nonconjugacy
-- statement:
--   The Quaternion Generators construction uses the psl total nonconjugacy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionPSLGenerators.lean#L98-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionPSLGenerators.lean#L98-L106

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionPSLGenerators
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
variable (f : F →+* K) (epsilon : F) (r y s i : K)
  (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = f epsilon)
  (hR : r ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
  (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
  (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1)
local notation "E" => projectiveMatrixEquivOfRoot (f epsilon) r y hRoot hR hOne hTwo
local notation "L" => indexedLeft f epsilon y hTwoF hY hOne hTwo
local notation "R" => indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo
include hEpsilon hRatio hI
local notation "PL" => pslLeft f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
local notation "PR" => pslRight f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.psl_total_nonconjugacy (a b : TorusIndex epsilon)
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) : PL a * g ≠ g * PR b := by sorry
