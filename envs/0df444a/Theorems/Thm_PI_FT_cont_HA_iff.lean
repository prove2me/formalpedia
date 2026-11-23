-- Prove2me | Theorems.Thm_PI_FT_cont_HA_iff
-- name    : PI.FT.cont_HA_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:52.788847+00:00
-- url     : https://prove2.me/theorems/d84ea43b-7c3c-4ae8-ab3a-841aee34493e
-- title:
--   FT: cont HA iff
-- statement:
--   The FT construction uses the cont HA iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean#L49-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem PI.FT.cont_HA_iff {T : Type*} [TopologicalSpace T] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (f : T → HA R σ J) :
    Continuous f ↔ Continuous (fun t => mt (f t)) ∧ Continuous (fun t => mtI (f t)) := by sorry
