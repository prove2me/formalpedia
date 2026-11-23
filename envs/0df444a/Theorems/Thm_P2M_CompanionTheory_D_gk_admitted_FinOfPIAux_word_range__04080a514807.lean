-- Prove2me | Theorems.Thm_P2M_CompanionTheory_D_gk_admitted_FinOfPIAux_word_range__04080a514807
-- name    : P2M_CompanionTheory_D_gk_admitted_FinOfPIAux_word_range__04080a514807
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:28.263899+00:00
-- url     : https://prove2.me/theorems/b285dc1a-d86a-40d3-88b2-a887ac96ec95
-- title:
--   P2 M Companion Theory D gk admitted Fin Of PIAux word range  04080a514807: P2 M Companion Theory D gk admitted Fin Of PIAux word range  04080a514807
-- statement:
--   The P2 M Companion Theory D gk admitted Fin Of PIAux word range  04080a514807 construction uses the P2 M Companion Theory D gk admitted Fin Of PIAux word range  04080a514807 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L208-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L208-L215

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (E : H →L[ℂ] H) (M : ℕ) (φ : ℕ → H →L[ℂ] ℂ) (x : ℕ → H)
omit [CompleteSpace H]

theorem P2M_CompanionTheory_D_gk_admitted_FinOfPIAux_word_range__04080a514807 (hφ : ∀ i ≤ M, ∀ j ≤ M, φ i (E (x j)) = if i = j then 1 else 0) (n k : ℕ) (hk : k + n = M) :
    word E ((List.range' k n).map fun a => (φ (a + 1)).smulRight (x a)) (x M) = E (x k) := by sorry

alias «CompanionTheory».«D».«gk».«admitted».«FinOfPIAux».«word_range'» := P2M_CompanionTheory_D_gk_admitted_FinOfPIAux_word_range__04080a514807
