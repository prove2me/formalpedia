-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_LocalizedFibreSets_starO___c01796a1051a
-- name    : P2M_Formalism_L2_SG_Pf_LocalizedFibreSets_starO___c01796a1051a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:38.361106+00:00
-- url     : https://prove2.me/theorems/4947d387-5f55-5583-b235-5a9d0715f25f
-- title:
--   P2 M Formalism L2 SG Pf Localized Fibre Sets star O   c01796a1051a: P2 M Formalism L2 SG Pf Localized Fibre Sets star O   c01796a1051a
-- statement:
--   The P2 M Formalism L2 SG Pf Localized Fibre Sets star O   c01796a1051a construction uses the P2 M Formalism L2 SG Pf Localized Fibre Sets star O   c01796a1051a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardPhiSucc.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardPhiSucc.lean#L18-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem P2M_Formalism_L2_SG_Pf_LocalizedFibreSets_starO___c01796a1051a (a : 𝓞 F) : star (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap (𝓞 F) (𝓞 K) a := by sorry

alias «Formalism».«L2».«SG».«Pf».«LocalizedFibreSets».«starO_ι» := P2M_Formalism_L2_SG_Pf_LocalizedFibreSets_starO___c01796a1051a
