-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_ratV_mem_spanR
-- name    : PI.VolSemiDirect.W.ratV_mem_spanR
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:49.509585+00:00
-- url     : https://prove2.me/theorems/0655b2ef-2ba2-514c-9981-aec6d7b118f5
-- title:
--   W: rat V mem span R
-- statement:
--   The W construction uses the rat V mem span R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L36-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L36-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_Closed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R}

theorem PI.VolSemiDirect.W.ratV_mem_spanR {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Y '' s)) : ratV (F := F) R x ∈ spanR (F := F) R Y s := by sorry
