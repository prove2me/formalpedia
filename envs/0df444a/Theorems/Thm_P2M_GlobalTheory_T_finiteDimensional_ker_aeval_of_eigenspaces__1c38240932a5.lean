-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_finiteDimensional_ker_aeval_of_eigenspaces__1c38240932a5
-- name    : P2M_GlobalTheory_T_finiteDimensional_ker_aeval_of_eigenspaces__1c38240932a5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:21.190239+00:00
-- url     : https://prove2.me/theorems/a6cf2f5a-25b0-4602-b2fa-85986a56933b
-- title:
--   P2 M Global Theory T finite Dimensional ker aeval of eigenspaces  1c38240932a5: P2 M Global Theory T finite Dimensional ker aeval of eigenspaces  1c38240932a5
-- statement:
--   The P2 M Global Theory T finite Dimensional ker aeval of eigenspaces  1c38240932a5 construction uses the P2 M Global Theory T finite Dimensional ker aeval of eigenspaces  1c38240932a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalKerAevalOfEigenspacesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalKerAevalOfEigenspacesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalKerAevalOfEigenspaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalKerAevalOfEigenspacesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_finiteDimensional_ker_aeval_of_eigenspaces__1c38240932a5 : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M), (∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) → ∀ p : Polynomial ℂ, p ≠ 0 → FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by sorry

alias «GlobalTheory».«T».«finiteDimensional_ker_aeval_of_eigenspaces'» := P2M_GlobalTheory_T_finiteDimensional_ker_aeval_of_eigenspaces__1c38240932a5
