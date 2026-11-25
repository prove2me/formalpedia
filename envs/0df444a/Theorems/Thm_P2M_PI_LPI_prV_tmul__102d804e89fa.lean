-- Prove2me | Theorems.Thm_P2M_PI_LPI_prV_tmul__102d804e89fa
-- name    : P2M_PI_LPI_prV_tmul__102d804e89fa
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:27.469516+00:00
-- url     : https://prove2.me/theorems/52c0a732-05e4-531e-80f9-7522e2e3e69e
-- title:
--   P2 M PI LPI pr V tmul  102d804e89fa: P2 M PI LPI pr V tmul  102d804e89fa
-- statement:
--   The P2 M PI LPI pr V tmul  102d804e89fa construction uses the P2 M PI LPI pr V tmul  102d804e89fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/PrVMemTensInt.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/PrVMemTensInt.lean#L11-L13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVMemTensInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
noncomputable section
open PI PI.LPI

theorem P2M_PI_LPI_prV_tmul__102d804e89fa {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] (a v) := by sorry

alias «PI».«LPI».«prV_tmul'» := P2M_PI_LPI_prV_tmul__102d804e89fa
