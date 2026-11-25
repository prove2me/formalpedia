-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_mem_Asub
-- name    : PI.LevelKSplit.W.NCL.mem_Asub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:50.141642+00:00
-- url     : https://prove2.me/theorems/96835bfb-af2a-451e-9879-1ec9728d6412
-- title:
--   NCL: mem Asub
-- statement:
--   The NCL construction uses the mem Asub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/IsClosedAsub.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/IsClosedAsub.lean#L19-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_IsClosedAsub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r}

theorem PI.LevelKSplit.W.NCL.mem_Asub {g : HA R σ J} : g ∈ Asub R σ J P ↔ (g ∈ Nsub R σ J P ∧
    (∀ w ∈ Wp R σ J P, lin R σ J g w = w) ∧
    (∀ b, lin R σ J g (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ) ∧
    (∀ b, lin R σ J g⁻¹ (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ)) := by sorry
