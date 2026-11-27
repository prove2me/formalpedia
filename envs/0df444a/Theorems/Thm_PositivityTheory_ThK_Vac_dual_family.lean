-- Prove2me | Theorems.Thm_PositivityTheory_ThK_Vac_dual_family
-- name    : PositivityTheory.ThK.Vac.dual_family
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:22.945052+00:00
-- url     : https://prove2.me/theorems/50980b5f-2b5d-46be-b0ac-d40d5616e7ed
-- title:
--   Vac: dual family
-- statement:
--   The Vac construction uses the dual family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/VaceigenAlg.lean#L10-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/VaceigenAlg.lean#L10-L47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_VaceigenAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.Vac
open scoped nonZeroDivisors Matrix

theorem PositivityTheory.ThK.Vac.dual_family (R K : Type) {V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] (L : Submodule R V) (hfg : L.FG)
    (hsp : Submodule.span K (L : Set V) = ⊤) :
    ∃ (m : ℕ) (g : Fin m → V) (f : Fin m → V →ₗ[K] K), (∀ i, g i ∈ L) ∧ (∀ i, ∀ x ∈ L, ∃ r : R, algebraMap R K r = f i x) ∧
      ∀ x, x = ∑ i, f i x • g i := by sorry
