-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry_squareComplex_hasCayleyLinkIdentities
-- name    : QEC.Coding.QuantumTanner.ArithmeticPSLGeometry.squareComplex_hasCayleyLinkIdentities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:01:26.662608+00:00
-- url     : https://prove2.me/theorems/b6837df0-c477-4267-ab38-a04f2077f407
-- title:
--   Arithmetic PSLGeometry: square Complex has Cayley Link Identities
-- statement:
--   The four-corner incidence laws required by the global distance argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLGeometry.lean#L54-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticPSLGeometry.lean#L54-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionPSLGenerators
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype F] [Fintype K]
variable (f : F →+* K) (epsilon : F) (r y s i : K)
  (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = f epsilon)
  (hR : r ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
  (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
  (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1)
local notation "L" => pslLeft f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
local notation "R" => pslRight f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI

theorem QEC.Coding.QuantumTanner.ArithmeticPSLGeometry.squareComplex_hasCayleyLinkIdentities :
    (squareComplex f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI).HasCayleyLinkIdentities := by sorry
