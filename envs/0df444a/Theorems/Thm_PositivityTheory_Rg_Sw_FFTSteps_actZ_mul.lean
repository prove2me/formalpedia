-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_actZ_mul
-- name    : PositivityTheory.Rg.Sw.FFTSteps.actZ_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:34.23071+00:00
-- url     : https://prove2.me/theorems/f7e261bc-5c3d-4e51-a230-1593a1831d09
-- title:
--   FFTSteps: act Z mul
-- statement:
--   The FFTSteps construction uses the act Z mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L90-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L90-L97

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
omit [DecidableEq ι]

theorem PositivityTheory.Rg.Sw.FFTSteps.actZ_mul (g h g' h' : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actZ (g * g') (h * h') z = actZ g h (actZ g' h' z) := by sorry
