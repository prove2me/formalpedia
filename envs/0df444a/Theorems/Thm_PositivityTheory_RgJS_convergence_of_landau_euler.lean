-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_convergence_of_landau_euler
-- name    : PositivityTheory.RgJS.convergence_of_landau_euler
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:45.150502+00:00
-- url     : https://prove2.me/theorems/e0433658-2298-4ace-a97b-aa5aa11900fc
-- title:
--   Rg JS: convergence of landau euler
-- statement:
--   The Rg JS construction uses the convergence of landau euler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L92-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L92-L131

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open DiagonalEntryNormBounds

theorem PositivityTheory.RgJS.convergence_of_landau_euler : LandauL → EulerLog → Conv1 := by sorry
