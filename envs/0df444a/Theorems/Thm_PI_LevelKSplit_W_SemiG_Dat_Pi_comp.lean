-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_Pi_comp
-- name    : PI.LevelKSplit.W.SemiG.Dat.Pi_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:22.269669+00:00
-- url     : https://prove2.me/theorems/c0a143b0-ff4f-44c6-a8d1-5b1eef21755f
-- title:
--   Dat: Pi comp
-- statement:
--   The Dat construction uses the Pi comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L89-L94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}

theorem PI.LevelKSplit.W.SemiG.Dat.Pi_comp (H : D.Hyp) {S S' : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) (hW' : D.MapW S')
    (v : n → A) : D.Pi S (D.Pi S' v) = D.Pi (S ∘ₗ S') v := by sorry
