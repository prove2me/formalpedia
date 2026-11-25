-- Prove2me | Theorems.Thm_P2M_Formalism_AtG_wt_nonneg__3d7a0657db25
-- name    : P2M_Formalism_AtG_wt_nonneg__3d7a0657db25
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:09.367669+00:00
-- url     : https://prove2.me/theorems/f6b758d9-c60e-4581-961b-516c443dd736
-- title:
--   P2 M Formalism At G wt nonneg  3d7a0657db25: P2 M Formalism At G wt nonneg  3d7a0657db25
-- statement:
--   The P2 M Formalism At G wt nonneg  3d7a0657db25 construction uses the P2 M Formalism At G wt nonneg  3d7a0657db25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ExponentGrids/ExponentGridsProofs/FrameHeightOfDualSlope.lean#L278-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ExponentGrids/ExponentGridsProofs/FrameHeightOfDualSlope.lean#L278-L285

import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Definitions.Def_Lemmata_PlaneOverMembership_PlOverOfMem
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_FrameHeightOfDualSlope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)
noncomputable section
open Formalism Formalism.AtG

theorem P2M_Formalism_AtG_wt_nonneg__3d7a0657db25 {K : Type} [Field K] [NumberField K] [StarRing K] (S : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ l ∈ S, 0 ≤ c l) (w : Pl K) : 0 ≤ wt S c w := by sorry

alias «Formalism».«AtG».«wt_nonneg'» := P2M_Formalism_AtG_wt_nonneg__3d7a0657db25
