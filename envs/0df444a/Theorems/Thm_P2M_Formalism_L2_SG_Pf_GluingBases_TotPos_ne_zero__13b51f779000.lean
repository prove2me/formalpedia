-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_GluingBases_TotPos_ne_zero__13b51f779000
-- name    : P2M_Formalism_L2_SG_Pf_GluingBases_TotPos_ne_zero__13b51f779000
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:42.464417+00:00
-- url     : https://prove2.me/theorems/bcec6069-33f2-4b4d-b273-ec5f1c4219b1
-- title:
--   P2 M Formalism L2 SG Pf Gluing Bases Tot Pos ne zero  13b51f779000: P2 M Formalism L2 SG Pf Gluing Bases Tot Pos ne zero  13b51f779000
-- statement:
--   The P2 M Formalism L2 SG Pf Gluing Bases Tot Pos ne zero  13b51f779000 construction uses the P2 M Formalism L2 SG Pf Gluing Bases Tot Pos ne zero  13b51f779000 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPrescFamily.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPrescFamily.lean#L33-L38

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPrescFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem P2M_Formalism_L2_SG_Pf_GluingBases_TotPos_ne_zero__13b51f779000 {x : K} (hx : TotPos x) : x ≠ 0 := by sorry

alias «Formalism».«L2».«SG».«Pf».«GluingBases».«TotPos».«ne_zero'» := P2M_Formalism_L2_SG_Pf_GluingBases_TotPos_ne_zero__13b51f779000
