-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower2_d91edae1b020
-- name    : P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower2_d91edae1b020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:17.153914+00:00
-- url     : https://prove2.me/theorems/b719e5f2-b1c0-42e3-a311-cf2b92e3b915
-- title:
--   P2 M Formalism Invariant Factor Paths Branching Dimensions f T  lower2 d91edae1b020: P2 M Formalism Invariant Factor Paths Branching Dimensions f T  lower2 d91edae1b020
-- statement:
--   The P2 M Formalism Invariant Factor Paths Branching Dimensions f T  lower2 d91edae1b020 construction uses the P2 M Formalism Invariant Factor Paths Branching Dimensions f T  lower2 d91edae1b020 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogBinomialProperties.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogBinomialProperties.lean#L95-L99

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters

theorem P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower2_d91edae1b020 (k' : ℕ) (y : ℝ) (hy : (k' : ℝ) ≤ y) (hk : 1 ≤ k') :
    (k' : ℝ) / (2 * y) ≤ fT' k' y := by sorry

alias «Formalism».«InvariantFactorPaths».«BranchingDimensions».«fT'_lower2» := P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower2_d91edae1b020
