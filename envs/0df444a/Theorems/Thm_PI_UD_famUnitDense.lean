-- Prove2me | Theorems.Thm_PI_UD_famUnitDense
-- name    : PI.UD.famUnitDense
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:49.750705+00:00
-- url     : https://prove2.me/theorems/1eb077aa-ba0c-4ab0-90bc-d4b137b1690b
-- title:
--   UD: fam Unit Dense
-- statement:
--   The UD construction uses the fam Unit Dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/VanishInvertible.lean#L31-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/VanishInvertible.lean#L31-L74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_VanishInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD

theorem PI.UD.famUnitDense (hs : SVDStep) {ι : Type} [Fintype ι] {n : ℕ}
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * y τ = 1) →
      eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) : P = 0 := by sorry
