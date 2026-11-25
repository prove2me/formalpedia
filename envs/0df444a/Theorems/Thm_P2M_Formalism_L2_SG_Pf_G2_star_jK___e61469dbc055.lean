-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G2_star_jK___e61469dbc055
-- name    : P2M_Formalism_L2_SG_Pf_G2_star_jK___e61469dbc055
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:38.786657+00:00
-- url     : https://prove2.me/theorems/5c90b312-44a2-5ac5-879c-d714d7bc9d5a
-- title:
--   P2 M Formalism L2 SG Pf G2 star j K   e61469dbc055: P2 M Formalism L2 SG Pf G2 star j K   e61469dbc055
-- statement:
--   The P2 M Formalism L2 SG Pf G2 star j K   e61469dbc055 construction uses the P2 M Formalism L2 SG Pf G2 star j K   e61469dbc055 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsSubDivMemSP.lean#L127-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsSubDivMemSP.lean#L127-L128

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

theorem P2M_Formalism_L2_SG_Pf_G2_star_jK___e61469dbc055 (hF : IsFixF K F) (t : 𝓞 F) : star (jK (ι t)) = jK (ι t) := by sorry

alias «Formalism».«L2».«SG».«Pf».«G2».«star_jK_ι» := P2M_Formalism_L2_SG_Pf_G2_star_jK___e61469dbc055
