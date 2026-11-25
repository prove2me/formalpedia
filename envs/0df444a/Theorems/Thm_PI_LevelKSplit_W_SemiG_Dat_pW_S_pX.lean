-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_S_pX
-- name    : PI.LevelKSplit.W.SemiG.Dat.pW_S_pX
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:36:58.561904+00:00
-- url     : https://prove2.me/theorems/e8440d0c-4047-50c6-a06e-0fb7b1961211
-- title:
--   Dat: p W S p X
-- statement:
--   The Dat construction uses the p W S p X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L74-L76

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

theorem PI.LevelKSplit.W.SemiG.Dat.pW_S_pX (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) (u : n → A) :
    D.pW (S (D.pX u)) = 0 := by sorry
