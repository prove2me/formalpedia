-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveLinearSize_projectiveUpper_injective
-- name    : QEC.Coding.ExpanderCodes.ProjectiveLinearSize.projectiveUpper_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:45:33.439381+00:00
-- url     : https://prove2.me/theorems/dda535c6-63ba-4f66-a62d-a64121d271c8
-- title:
--   Projective Linear Size: projective Upper injective
-- statement:
--   Passing to the projective quotient does not identify distinct unipotents.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean#L30-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean#L30-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveLinearSize
open Matrix
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.ProjectiveLinearSize.projectiveUpper_injective : Function.Injective (projectiveUpper (K := K)) := by sorry
