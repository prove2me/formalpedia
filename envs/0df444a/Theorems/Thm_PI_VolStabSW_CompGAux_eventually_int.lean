-- Prove2me | Theorems.Thm_PI_VolStabSW_CompGAux_eventually_int
-- name    : PI.VolStabSW.CompGAux.eventually_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:23.451884+00:00
-- url     : https://prove2.me/theorems/3fa0bf49-0187-4ac0-be66-4582af7515c3
-- title:
--   Comp GAux: eventually int
-- statement:
--   The Comp GAux construction uses the eventually int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean#L108-L114

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

theorem PI.VolStabSW.CompGAux.eventually_int (g : HA (AF F) σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ i j p, piV F v (crd b (AF F)
      (((HA.mat (AF F) σ J g : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
        v.adicCompletionIntegers F := by sorry
