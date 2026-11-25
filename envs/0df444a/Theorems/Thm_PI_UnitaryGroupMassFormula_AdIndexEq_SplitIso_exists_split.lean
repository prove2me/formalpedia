-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitIso_exists_split
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.exists_split
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:38:40.758587+00:00
-- url     : https://prove2.me/theorems/2b2eccf2-eebd-464f-96a3-cd6a90b2b7a2
-- title:
--   Split Iso: exists split
-- statement:
--   The Split Iso construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitIso.lean#L45-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitIso.lean#L45-L208

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
open scoped TensorProduct
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
variable (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2)
    (h2K : (2 : K) ≠ 0)
include hσσ hfix h2 h2K

theorem PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.exists_split (hnf : ¬ IsField (K ⊗[F] E)) :
    ∃ π : K ⊗[F] E ≃+* K × K, ∀ r, π (sigT σ r) = (π r).swap := by sorry
