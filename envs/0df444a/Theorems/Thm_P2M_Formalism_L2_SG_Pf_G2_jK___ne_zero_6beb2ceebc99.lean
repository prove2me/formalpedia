-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G2_jK___ne_zero_6beb2ceebc99
-- name    : P2M_Formalism_L2_SG_Pf_G2_jK___ne_zero_6beb2ceebc99
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:53.985375+00:00
-- url     : https://prove2.me/theorems/8d623532-b65c-59d7-a316-1518b7453e7a
-- title:
--   P2 M Formalism L2 SG Pf G2 j K   ne zero 6beb2ceebc99: P2 M Formalism L2 SG Pf G2 j K   ne zero 6beb2ceebc99
-- statement:
--   The P2 M Formalism L2 SG Pf G2 j K   ne zero 6beb2ceebc99 construction uses the P2 M Formalism L2 SG Pf G2 j K   ne zero 6beb2ceebc99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsSubDivMemSP.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsSubDivMemSP.lean#L23-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsSubDivMemSP
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G2
open Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem P2M_Formalism_L2_SG_Pf_G2_jK___ne_zero_6beb2ceebc99 {t : 𝓞 F} (ht : t ≠ 0) : jK (ι t) ≠ 0 := by sorry

alias «Formalism».«L2».«SG».«Pf».«G2».«jK_ι_ne_zero» := P2M_Formalism_L2_SG_Pf_G2_jK___ne_zero_6beb2ceebc99
