-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_actZ_diagonal
-- name    : PositivityTheory.Rg.Sw.FFTSteps.actZ_diagonal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:04.599025+00:00
-- url     : https://prove2.me/theorems/7452ce86-746b-50ad-94d4-fe475b238e1e
-- title:
--   FFTSteps: act Z diagonal
-- statement:
--   The FFTSteps construction uses the act Z diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L99-L104

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ExistsUnitaryDiagonalUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

theorem PositivityTheory.Rg.Sw.FFTSteps.actZ_diagonal (a b : ι → ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actZ (diagonal a) (diagonal b) z = Sum.elim (fun x => a x.1 * z (Sum.inl x)) (fun y => b y.1 * z (Sum.inr y)) := by sorry
