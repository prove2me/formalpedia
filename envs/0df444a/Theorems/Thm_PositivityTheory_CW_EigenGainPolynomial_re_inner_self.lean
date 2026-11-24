-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenGainPolynomial_re_inner_self
-- name    : PositivityTheory.CW.EigenGainPolynomial.re_inner_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:45.134056+00:00
-- url     : https://prove2.me/theorems/b898b76d-f241-4384-a453-5901c57aeefa
-- title:
--   Eigen Gain Polynomial: re inner self
-- statement:
--   The Eigen Gain Polynomial construction uses the re inner self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisFormSumOfGain.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisFormSumOfGain.lean#L11-L14

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisFormSumOfGain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenGainPolynomial

theorem PositivityTheory.CW.EigenGainPolynomial.re_inner_self {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (w : V) :
    (inner ℂ w w).re = ‖w‖ ^ 2 := by sorry
