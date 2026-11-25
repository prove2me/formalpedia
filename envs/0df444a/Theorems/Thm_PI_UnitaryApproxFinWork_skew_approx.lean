-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_skew_approx
-- name    : PI.UnitaryApproxFinWork.skew_approx
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:31:32.113064+00:00
-- url     : https://prove2.me/theorems/7cacf86c-eb5e-4dfa-86d5-1d95e56f3213
-- title:
--   Unitary Approx Fin Work: skew approx
-- statement:
--   The Unitary Approx Fin Work construction uses the skew approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/SkewApprox.lean#L17-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/SkewApprox.lean#L17-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Cayley
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SkewApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork

theorem PI.UnitaryApproxFinWork.skew_approx (hAE : ApproxE) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (Y : (v : HeightOneSpectrum (𝓞 F)) → Matrix n n (E ⊗[F] v.adicCompletion F))
    (hY : ∀ v ∈ T, PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (Y v) = -Y v) (δ : 𝓞 F) (hδ : δ ≠ 0) :
    ∃ Y' : Matrix n n E, PI.UnitaryApproxDefs.cT (σ : E →+* E) Y' = -Y' ∧
      ∀ v ∈ T, MC E v δ (Y'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) - Y v) := by sorry
