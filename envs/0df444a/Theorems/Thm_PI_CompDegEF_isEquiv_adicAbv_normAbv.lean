-- Prove2me | Theorems.Thm_PI_CompDegEF_isEquiv_adicAbv_normAbv
-- name    : PI.CompDegEF.isEquiv_adicAbv_normAbv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:57:23.541135+00:00
-- url     : https://prove2.me/theorems/04adb09b-cff9-4439-a616-ddd3b4732840
-- title:
--   Comp Deg EF: is Equiv adic Abv norm Abv
-- statement:
--   The Comp Deg EF construction uses the is Equiv adic Abv norm Abv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/IsEquivAdicAbvNormAbv.lean#L96-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/IsEquivAdicAbvNormAbv.lean#L96-L104

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_IsEquivAdicAbvNormAbv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem PI.CompDegEF.isEquiv_adicAbv_normAbv {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ placesOver E l)
    (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ 1 ∧ (‖φ (x : E)‖ < 1 ↔ x ∈ v.asIdeal)) :
    (v.adicAbv (K := E) (b := 2) one_lt_two).IsEquiv (normAbv φ) := by sorry
