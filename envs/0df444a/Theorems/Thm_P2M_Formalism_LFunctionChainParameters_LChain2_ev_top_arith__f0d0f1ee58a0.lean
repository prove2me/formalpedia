-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_LChain2_ev_top_arith__f0d0f1ee58a0
-- name    : P2M_Formalism_LFunctionChainParameters_LChain2_ev_top_arith__f0d0f1ee58a0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:04.827311+00:00
-- url     : https://prove2.me/theorems/3bd2ed1f-cd19-4106-940b-480dcfd8f4cc
-- title:
--   P2 M Formalism LFunction Chain Parameters LChain2 ev top arith  f0d0f1ee58a0: P2 M Formalism LFunction Chain Parameters LChain2 ev top arith  f0d0f1ee58a0
-- statement:
--   The P2 M Formalism LFunction Chain Parameters LChain2 ev top arith  f0d0f1ee58a0 construction uses the P2 M Formalism LFunction Chain Parameters LChain2 ev top arith  f0d0f1ee58a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L2337-L2341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L2337-L2341

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain2
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)

theorem P2M_Formalism_LFunctionChainParameters_LChain2_ev_top_arith__f0d0f1ee58a0 (c m A lA lT lg γ lx xe l2 : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlg : m * lg = lT - m * (l2 + xe)) (hlA : lA = lx + xe) (h : 2 + γ + l2 ≤ lx) :
    c * (m * A) ≤ c * (m * ((A * lA - A) - A * γ) - A * lT) + m * (c * A) * lg := by sorry

alias «Formalism».«LFunctionChainParameters».«LChain2».«ev_top_arith'» := P2M_Formalism_LFunctionChainParameters_LChain2_ev_top_arith__f0d0f1ee58a0
