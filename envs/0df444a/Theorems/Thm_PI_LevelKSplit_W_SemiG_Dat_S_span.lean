-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_S_span
-- name    : PI.LevelKSplit.W.SemiG.Dat.S_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:55.857326+00:00
-- url     : https://prove2.me/theorems/0182b936-cf4f-461a-8c81-5f7338bdeab3
-- title:
--   Dat: S span
-- statement:
--   The Dat construction uses the S span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean#L68-L72

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

theorem PI.LevelKSplit.W.SemiG.Dat.S_span {S : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : S x ∈ Submodule.span A (Set.range D.e) := by sorry
