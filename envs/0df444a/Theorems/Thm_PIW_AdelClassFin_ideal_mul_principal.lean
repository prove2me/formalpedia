-- Prove2me | Theorems.Thm_PIW_AdelClassFin_ideal_mul_principal
-- name    : PIW.AdelClassFin.ideal_mul_principal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:14.833291+00:00
-- url     : https://prove2.me/theorems/d8c61f51-20d2-49ef-ad2e-d0473c05eab4
-- title:
--   Adel Class Fin: ideal mul principal
-- statement:
--   The Adel Class Fin construction uses the ideal mul principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IdealMulPrincipal.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IdealMulPrincipal.lean#L10-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField
open scoped nonZeroDivisors

theorem PIW.AdelClassFin.ideal_mul_principal {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI0 : I ∈ (Ideal (𝓞 E))⁰)
    (A : (Ideal (𝓞 E))⁰) (hA : ClassGroup.mk0 A = (ClassGroup.mk0 (⟨I, hI0⟩ : (Ideal (𝓞 E))⁰))⁻¹) :
    ∃ c : 𝓞 E, I * (A : Ideal (𝓞 E)) = Ideal.span {c} := by sorry
