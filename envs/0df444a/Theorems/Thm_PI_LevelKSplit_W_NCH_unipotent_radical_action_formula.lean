-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_unipotent_radical_action_formula
-- name    : PI.LevelKSplit.W.NCH.unipotent_radical_action_formula
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:34:56.28909+00:00
-- url     : https://prove2.me/theorems/6855256c-1a4c-4acc-9dc5-c66a2dcbd4af
-- title:
--   NCH: unipotent radical action formula
-- statement:
--   The NCH construction uses the unipotent radical action formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L263-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L263-L296

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

theorem PI.LevelKSplit.W.NCH.unipotent_radical_action_formula (H : D.Hyp) {Φ : (n → A) →ₗ[A] (n → A)} (hU : D.Uni Φ) (he : ∀ a, Φ (D.e a) = D.e a)
    (hP : ∀ v, Xp D v → Φ v - v ∈ Submodule.span A (Set.range D.e)) {v : n → A} (hv : Xp D v) :
    Φ v = v - ∑ a, D.h (pWp D (Φ (D.f a))) v • D.e a := by sorry
