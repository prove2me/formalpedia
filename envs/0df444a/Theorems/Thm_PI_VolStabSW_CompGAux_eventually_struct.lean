-- Prove2me | Theorems.Thm_PI_VolStabSW_CompGAux_eventually_struct
-- name    : PI.VolStabSW.CompGAux.eventually_struct
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:27.820092+00:00
-- url     : https://prove2.me/theorems/17de11fe-243b-48ec-9be1-7fca726565ee
-- title:
--   Comp GAux: eventually struct
-- statement:
--   The Comp GAux construction uses the eventually struct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean#L116-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean#L116-L125

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallyStruct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.CompGAux
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabSW.FiniteThetaCoordinates
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem PI.VolStabSW.CompGAux.eventually_struct {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ p q k,
      algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F := by sorry
