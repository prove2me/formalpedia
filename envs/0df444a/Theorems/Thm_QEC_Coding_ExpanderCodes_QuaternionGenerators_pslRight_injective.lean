-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslRight_injective
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.pslRight_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:40:37.675805+00:00
-- url     : https://prove2.me/theorems/f6c8841e-08c8-4876-bed5-edc859a37b6f
-- title:
--   Quaternion Generators: psl Right injective
-- statement:
--   The Quaternion Generators construction uses the psl Right injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionPSLGenerators.lean#L79-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionPSLGenerators.lean#L79-L84

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.pslRight_injective : Function.Injective PR := by sorry
