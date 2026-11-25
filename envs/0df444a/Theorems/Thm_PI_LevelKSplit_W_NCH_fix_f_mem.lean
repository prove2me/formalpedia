-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_fix_f_mem
-- name    : PI.LevelKSplit.W.NCH.fix_f_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:18.144319+00:00
-- url     : https://prove2.me/theorems/c9d12a98-7ddf-5d09-81bb-70553c54ebed
-- title:
--   NCH: fix f mem
-- statement:
--   The NCH construction uses the fix f mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L300-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L300-L345

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}

theorem PI.LevelKSplit.W.NCH.fix_f_mem (H : D.Hyp) (hND : ND D) {Φ : (n → A) →ₗ[A] (n → A)} (hU : D.Uni Φ)
    (hfix : ∀ v, Xp D v → Φ v = v) (a : Fin r) :
    Φ (D.f a) - D.f a ∈ Submodule.span A (Set.range D.e) := by sorry
