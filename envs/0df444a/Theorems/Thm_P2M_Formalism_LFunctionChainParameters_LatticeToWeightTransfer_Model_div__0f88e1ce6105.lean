-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_div__0f88e1ce6105
-- name    : P2M_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_div__0f88e1ce6105
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:50.268149+00:00
-- url     : https://prove2.me/theorems/6c7e68a3-c321-5b5e-af45-eadad0979b9d
-- title:
--   P2 M Formalism LFunction Chain Parameters Lattice To Weight Transfer Model div  0f88e1ce6105: P2 M Formalism LFunction Chain Parameters Lattice To Weight Transfer Model div  0f88e1ce6105
-- statement:
--   The P2 M Formalism LFunction Chain Parameters Lattice To Weight Transfer Model div  0f88e1ce6105 construction uses the P2 M Formalism LFunction Chain Parameters Lattice To Weight Transfer Model div  0f88e1ce6105 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SlopeInequalityOfLattices.lean#L354-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SlopeInequalityOfLattices.lean#L354-L362

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model

theorem P2M_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_div__0f88e1ce6105 (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : (D1 μ0 μ1 μ2 h).DIV C2 := by sorry

alias «Formalism».«LFunctionChainParameters».«LatticeToWeightTransfer».«Model».«div'» := P2M_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_div__0f88e1ce6105
