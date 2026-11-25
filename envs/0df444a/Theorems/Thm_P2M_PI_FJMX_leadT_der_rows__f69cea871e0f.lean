-- Prove2me | Theorems.Thm_P2M_PI_FJMX_leadT_der_rows__f69cea871e0f
-- name    : P2M_PI_FJMX_leadT_der_rows__f69cea871e0f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:56:40.503077+00:00
-- url     : https://prove2.me/theorems/26aaf4a2-754a-4986-a256-679d5c269ecf
-- title:
--   P2 M PI FJMX lead T der rows  f69cea871e0f: P2 M PI FJMX lead T der rows  f69cea871e0f
-- statement:
--   The P2 M PI FJMX lead T der rows  f69cea871e0f construction uses the P2 M PI FJMX lead T der rows  f69cea871e0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L15-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L15-L38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {A : Type*} [CommRing A] [Algebra ℂ A] {m k : ℕ}

theorem P2M_PI_FJMX_leadT_der_rows__f69cea871e0f (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (t : ℕ)
    (h : ∀ i₀ : Fin m, i₀.val < t → (∀ j : Fin k, j.val < t → D (M i₀ j) = 0) ∨
      ∃ i₁ : Fin m, i₁.val < t ∧ i₁ ≠ i₀ ∧ ∃ e : A, ∀ j : Fin k, j.val < t → D (M i₀ j) = e * M i₁ j) :
    D (PI.FJM.leadT M t) = 0 := by sorry

alias «PI».«FJMX».«leadT_der_rows'» := P2M_PI_FJMX_leadT_der_rows__f69cea871e0f
