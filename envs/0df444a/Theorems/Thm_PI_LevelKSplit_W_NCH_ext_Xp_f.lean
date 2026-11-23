-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_ext_Xp_f
-- name    : PI.LevelKSplit.W.NCH.ext_Xp_f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:03.923587+00:00
-- url     : https://prove2.me/theorems/36ffcb50-edc3-47af-bd9a-f7c8ee643e28
-- title:
--   NCH: ext Xp f
-- statement:
--   The NCH construction uses the ext Xp f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L169-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L169-L174

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

theorem PI.LevelKSplit.W.NCH.ext_Xp_f (H : D.Hyp) {Φ Ψ : (n → A) →ₗ[A] (n → A)} (h1 : ∀ v, Xp D v → Φ v = Ψ v)
    (h2 : ∀ a, Φ (D.f a) = Ψ (D.f a)) (v : n → A) : Φ v = Ψ v := by sorry
