-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Frob_tens_induction
-- name    : PositivityTheory.PfBern.Frob.tens_induction
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:44.942121+00:00
-- url     : https://prove2.me/theorems/e7b334da-8d4e-489f-a87a-5aebc08da4c0
-- title:
--   Frob: tens induction
-- statement:
--   The Frob construction uses the tens induction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/TensInduction.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/TensInduction.lean#L85-L93

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B]

theorem PositivityTheory.PfBern.Frob.tens_induction {M : Type*} [AddCommGroup M] [Module ℂ M] (T : SB (A × B) →ₗ[ℂ] M)
    (N : Submodule ℂ M) (f : SB (A × B))
    (h : ∀ (a : SB A) (b : SB B), (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 →
      (f : A × B → ℂ) q ≠ 0) → T (tens a b) ∈ N) : T f ∈ N := by sorry
