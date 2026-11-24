-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Ald_PCI_iteratedFDeriv_integral
-- name    : PositivityTheory.SiegelWeilFormula.Ald.PCI.iteratedFDeriv_integral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:11.493976+00:00
-- url     : https://prove2.me/theorems/2dcc0530-b56a-414d-ba3c-0d2f85b6d960
-- title:
--   PCI: iterated FDeriv integral
-- statement:
--   The PCI construction uses the iterated FDeriv integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LagrangianDecomposition/IteratedFDerivIntegral.lean#L34-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LagrangianDecomposition/IteratedFDerivIntegral.lean#L34-L57

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
variable [FiniteDimensional ℝ V]

theorem PositivityTheory.SiegelWeilFormula.Ald.PCI.iteratedFDeriv_integral {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (fun y => ∫ s in Ioc (0 : ℝ) 1, Θ (y, s)) x = ∫ s in Ioc (0 : ℝ) 1, pder n Θ (x, s) := by sorry
