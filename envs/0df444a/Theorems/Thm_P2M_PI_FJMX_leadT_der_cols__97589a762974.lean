-- Prove2me | Theorems.Thm_P2M_PI_FJMX_leadT_der_cols__97589a762974
-- name    : P2M_PI_FJMX_leadT_der_cols__97589a762974
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:56:09.665915+00:00
-- url     : https://prove2.me/theorems/68cd9ac7-8ce5-4c26-96b1-b5d685ea3978
-- title:
--   P2 M PI FJMX lead T der cols  97589a762974: P2 M PI FJMX lead T der cols  97589a762974
-- statement:
--   The P2 M PI FJMX lead T der cols  97589a762974 construction uses the P2 M PI FJMX lead T der cols  97589a762974 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L40-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L40-L63

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

theorem P2M_PI_FJMX_leadT_der_cols__97589a762974 (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (t : ℕ)
    (h : ∀ j₀ : Fin k, j₀.val < t → (∀ i : Fin m, i.val < t → D (M i j₀) = 0) ∨
      ∃ j₁ : Fin k, j₁.val < t ∧ j₁ ≠ j₀ ∧ ∃ e : A, ∀ i : Fin m, i.val < t → D (M i j₀) = e * M i j₁) :
    D (PI.FJM.leadT M t) = 0 := by sorry

alias «PI».«FJMX».«leadT_der_cols'» := P2M_PI_FJMX_leadT_der_cols__97589a762974
