-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_ell_mem
-- name    : PositivityTheory.Rg.Sw.FFTSteps.ell_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:55:01.557321+00:00
-- url     : https://prove2.me/theorems/2a81f9b9-2c5d-470b-8e64-9a5698525344
-- title:
--   FFTSteps: ell mem
-- statement:
--   The FFTSteps construction uses the ell mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L153-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L153-L158

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.FFTSteps.ell_mem (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ∈
      Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n)) := by sorry
