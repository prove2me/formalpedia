-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Ald_PCI_pder_eq
-- name    : PositivityTheory.SiegelWeilFormula.Ald.PCI.pder_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:38.351575+00:00
-- url     : https://prove2.me/theorems/33481f25-6f85-4fdf-9c7f-f356630201f9
-- title:
--   PCI: pder eq
-- statement:
--   The PCI construction uses the pder eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LagrangianDecomposition/IteratedFDerivIntegral.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LagrangianDecomposition/IteratedFDerivIntegral.lean#L16-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LagrangianDecomposition_IteratedFDerivIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open MeasureTheory Set Filter Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Ald PositivityTheory.SiegelWeilFormula.Ald.PCI
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem PositivityTheory.SiegelWeilFormula.Ald.PCI.pder_eq (n : ℕ) {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) (p : V × ℝ) :
    pder n Θ p = (iteratedFDeriv ℝ n Θ p).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ V ℝ) := by sorry
