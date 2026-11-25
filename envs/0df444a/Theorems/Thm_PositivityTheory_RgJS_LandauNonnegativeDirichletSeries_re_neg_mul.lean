-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_LandauNonnegativeDirichletSeries_re_neg_mul
-- name    : PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.re_neg_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:16.988691+00:00
-- url     : https://prove2.me/theorems/d47585aa-eadd-4b0e-bc5c-3b23e08d4593
-- title:
--   Landau Nonnegative Dirichlet Series: re neg mul
-- statement:
--   The Landau Nonnegative Dirichlet Series construction uses the re neg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean#L130-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean#L130-L130

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.LandauNonnegativeDirichletSeries

theorem PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.re_neg_mul (l : ℝ) (s : ℂ) : (-(l : ℂ) * s).re = -(l * s.re) := by sorry
