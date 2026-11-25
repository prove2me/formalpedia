-- Prove2me | Theorems.Thm_PI_VolStabW_rapidDecay_of_compact
-- name    : PI.VolStabW.rapidDecay_of_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:39.936933+00:00
-- url     : https://prove2.me/theorems/a614f354-6f2f-44e4-861f-33e56029ff76
-- title:
--   Vol Stab W: rapid Decay of compact
-- statement:
--   The Vol Stab W construction uses the rapid Decay of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SWeqOm.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SWeqOm.lean#L32-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SWeqOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem PI.VolStabW.rapidDecay_of_compact {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    RapidDecay b Φ := by sorry
