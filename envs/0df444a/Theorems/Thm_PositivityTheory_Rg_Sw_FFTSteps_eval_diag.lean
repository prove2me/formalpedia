-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_eval_diag
-- name    : PositivityTheory.Rg.Sw.FFTSteps.eval_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:55:14.823447+00:00
-- url     : https://prove2.me/theorems/522c891f-84a1-464b-b635-2bcffd4e9aaf
-- title:
--   FFTSteps: eval diag
-- statement:
--   The FFTSteps construction uses the eval diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L122-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L122-L177

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

theorem PositivityTheory.Rg.Sw.FFTSteps.eval_diag (p : PV ι A B) (hp : IsInv p) (a : ι → ℝ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval (actZ (diagonal fun i => cexp (a i)) (diagonal fun i => cexp (-(a i : ℂ))) z) p = eval z p := by sorry
