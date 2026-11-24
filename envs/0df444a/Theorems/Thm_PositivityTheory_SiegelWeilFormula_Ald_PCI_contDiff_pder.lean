-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Ald_PCI_contDiff_pder
-- name    : PositivityTheory.SiegelWeilFormula.Ald.PCI.contDiff_pder
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:11.853794+00:00
-- url     : https://prove2.me/theorems/462ef514-ed12-496b-8bee-596fe8cb00f8
-- title:
--   PCI: cont Diff pder
-- statement:
--   The PCI construction uses the cont Diff pder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LagrangianDecomposition/IteratedFDerivIntegral.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LagrangianDecomposition/IteratedFDerivIntegral.lean#L25-L30

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

theorem PositivityTheory.SiegelWeilFormula.Ald.PCI.contDiff_pder (n : ℕ) {Θ : V × ℝ → ℂ} (hΘ : ContDiff ℝ ∞ Θ) : ContDiff ℝ ∞ (pder n Θ) := by sorry
