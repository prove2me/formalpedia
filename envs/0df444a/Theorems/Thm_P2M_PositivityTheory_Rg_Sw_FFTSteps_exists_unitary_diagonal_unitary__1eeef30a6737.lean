-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_exists_unitary_diagonal_unitary__1eeef30a6737
-- name    : P2M_PositivityTheory_Rg_Sw_FFTSteps_exists_unitary_diagonal_unitary__1eeef30a6737
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:37.802683+00:00
-- url     : https://prove2.me/theorems/187fe42d-6995-5755-82eb-0ec82091ee40
-- title:
--   P2 M Positivity Theory Rg Sw FFTSteps exists unitary diagonal unitary  1eeef30a6737: P2 M Positivity Theory Rg Sw FFTSteps exists unitary diagonal unitary  1eeef30a6737
-- statement:
--   The P2 M Positivity Theory Rg Sw FFTSteps exists unitary diagonal unitary  1eeef30a6737 construction uses the P2 M Positivity Theory Rg Sw FFTSteps exists unitary diagonal unitary  1eeef30a6737 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L13-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ExistsUnitaryDiagonalUnitary.lean#L13-L72

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

theorem P2M_PositivityTheory_Rg_Sw_FFTSteps_exists_unitary_diagonal_unitary__1eeef30a6737 (g : Matrix ι ι ℂ) (hg : IsUnit g) :
    ∃ (u₁ u₂ : Matrix ι ι ℂ) (a : ι → ℝ), u₁ ∈ Matrix.unitaryGroup ι ℂ ∧
      u₂ ∈ Matrix.unitaryGroup ι ℂ ∧ g = u₁ * diagonal (fun i => cexp (a i)) * u₂ := by sorry

alias «PositivityTheory».«Rg».«Sw».«FFTSteps».«exists_unitary_diagonal_unitary'» := P2M_PositivityTheory_Rg_Sw_FFTSteps_exists_unitary_diagonal_unitary__1eeef30a6737
