-- Prove2me | Theorems.Thm_PI_VolStabW_fix2
-- name    : PI.VolStabW.fix2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:50:07.502802+00:00
-- url     : https://prove2.me/theorems/d8beb6bc-ff3a-596c-8b3d-1f2bfe57395d
-- title:
--   Vol Stab W: fix2
-- statement:
--   The Vol Stab W construction uses the fix2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxA.lean#L48-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxA.lean#L48-L107

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxA
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
open scoped TensorProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem PI.VolStabW.fix2 {F : Type} [Field F] (C : Matrix (Fin 2) (Fin 2) F) (hC : C ≠ 1) (u : Fin 2 → F)
    (hu : u ≠ 0) (hCu : Matrix.mulVec C u = u) :
    ∃ k0 k1 : Fin 2, k0 ≠ k1 ∧ u k0 ≠ 0 ∧ ∃ ρ : F, ∀ (K : Type) [Field K] [Algebra F K]
      (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → x k1 = algebraMap F K ρ * x k0 := by sorry
