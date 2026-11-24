-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_eval_inv
-- name    : PositivityTheory.Rg.Sw.FFTSteps.eval_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:09:22.695408+00:00
-- url     : https://prove2.me/theorems/1515f8d6-aeaa-469f-8f37-ae272437dad8
-- title:
--   FFTSteps: eval inv
-- statement:
--   The FFTSteps construction uses the eval inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L118-L120

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

theorem PositivityTheory.Rg.Sw.FFTSteps.eval_inv (p : PV ι A B) (hp : IsInv p) (u : Matrix ι ι ℂ) (hu : u ∈ Matrix.unitaryGroup ι ℂ)
    (z : (ι × A) ⊕ (ι × B) → ℂ) : eval (actZ u (u.map star) z) p = eval z p := by sorry
