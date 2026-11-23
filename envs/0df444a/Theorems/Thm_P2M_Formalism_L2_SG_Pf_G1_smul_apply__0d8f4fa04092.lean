-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G1_smul_apply__0d8f4fa04092
-- name    : P2M_Formalism_L2_SG_Pf_G1_smul_apply__0d8f4fa04092
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:07.572897+00:00
-- url     : https://prove2.me/theorems/95fa9dfc-2608-43bb-9a80-8c6b1df4652e
-- title:
--   P2 M Formalism L2 SG Pf G1 smul apply  0d8f4fa04092: P2 M Formalism L2 SG Pf G1 smul apply  0d8f4fa04092
-- statement:
--   The P2 M Formalism L2 SG Pf G1 smul apply  0d8f4fa04092 construction uses the P2 M Formalism L2 SG Pf G1 smul apply  0d8f4fa04092 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsOrthGen.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsOrthGen.lean#L22-L23

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K}

theorem P2M_Formalism_L2_SG_Pf_G1_smul_apply__0d8f4fa04092 (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) : (c • h) x y = c * h x y := by sorry

alias «Formalism».«L2».«SG».«Pf».«G1».«smul_apply'» := P2M_Formalism_L2_SG_Pf_G1_smul_apply__0d8f4fa04092
