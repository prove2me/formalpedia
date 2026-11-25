-- Prove2me | Theorems.Thm_PI_AprimeInfW_psi_mp
-- name    : PI.AprimeInfW.psi_mp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:35.08873+00:00
-- url     : https://prove2.me/theorems/e050ba48-452b-46ed-bb57-ba9e30f93093
-- title:
--   Aprime Inf W: psi mp
-- statement:
--   The Aprime Inf W construction uses the psi mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/MpOfIsomProd.lean#L126-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/MpOfIsomProd.lean#L126-L157

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MpOfIsomProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix ComplexConjugate

theorem PI.AprimeInfW.psi_mp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    MeasurePreserving (psiLp H) volume volume := by sorry
