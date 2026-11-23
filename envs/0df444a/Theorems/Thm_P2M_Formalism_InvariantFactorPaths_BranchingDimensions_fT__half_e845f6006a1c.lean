-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__half_e845f6006a1c
-- name    : P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__half_e845f6006a1c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:14.114055+00:00
-- url     : https://prove2.me/theorems/99df24c0-2d9f-435c-8de5-98fcc8029c6d
-- title:
--   P2 M Formalism Invariant Factor Paths Branching Dimensions f T  half e845f6006a1c: P2 M Formalism Invariant Factor Paths Branching Dimensions f T  half e845f6006a1c
-- statement:
--   The P2 M Formalism Invariant Factor Paths Branching Dimensions f T  half e845f6006a1c construction uses the P2 M Formalism Invariant Factor Paths Branching Dimensions f T  half e845f6006a1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogBinomialProperties.lean#L101-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LogBinomialProperties.lean#L101-L111

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

theorem P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__half_e845f6006a1c (k' : ℕ) (y y' : ℝ) (hy : (k' : ℝ) ≤ y) (h : 4 * y ≤ y') :
    fT' k' y' ≤ fT' k' y / 2 := by sorry

alias «Formalism».«InvariantFactorPaths».«BranchingDimensions».«fT'_half» := P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__half_e845f6006a1c
