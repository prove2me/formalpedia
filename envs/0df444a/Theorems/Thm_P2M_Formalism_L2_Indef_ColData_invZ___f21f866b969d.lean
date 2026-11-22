-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_ColData_invZ___f21f866b969d
-- name    : P2M_Formalism_L2_Indef_ColData_invZ___f21f866b969d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:00.450052+00:00
-- url     : https://prove2.me/theorems/f9853caf-3d1e-4caa-a5c8-cb12e7906b86
-- title:
--   P2 M Formalism L2 Indef Col Data inv Z   f21f866b969d: P2 M Formalism L2 Indef Col Data inv Z   f21f866b969d
-- statement:
--   The P2 M Formalism L2 Indef Col Data inv Z   f21f866b969d construction uses the P2 M Formalism L2 Indef Col Data inv Z   f21f866b969d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L31-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)

theorem P2M_Formalism_L2_Indef_ColData_invZ___f21f866b969d (u : Dc.Mem) (t : Bs.Tup) : C.invZ.ζ u t = (C.ζ u t)⁻¹ := by sorry

alias «Formalism».«L2».«Indef».«ColData».«invZ_ζ» := P2M_Formalism_L2_Indef_ColData_invZ___f21f866b969d

attribute [defeq] P2M_Formalism_L2_Indef_ColData_invZ___f21f866b969d
