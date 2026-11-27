-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_pre
-- name    : PI.SqPair.LocCartanPairW.cmp_pre
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:44.166475+00:00
-- url     : https://prove2.me/theorems/e7e380e5-ae50-512b-bb4f-2ece8ffcd8d7
-- title:
--   Loc Cartan Pair W: cmp pre
-- statement:
--   The Loc Cartan Pair W construction uses the cmp pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L52-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L52-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)

theorem PI.SqPair.LocCartanPairW.cmp_pre {ι : Type*} [Fintype ι] (h : Matrix ι ι R) (p q x y : ι → R) (c₁ d α' s' : R)
    (w : Matrix (Fin 2) (Fin 2) R) (hp : h *ᵥ p = c₁ • x) (hq : h *ᵥ q = (c₁ * d) • y)
    (hw : w 1 0 = d * α' * s') :
    h *ᵥ (w 0 0 • p + (s' * α') • q) = c₁ • (w 0 0 • x + w 1 0 • y) ∧
      h *ᵥ ((w 0 1 * d) • p + w 1 1 • q) = (c₁ * d) • (w 0 1 • x + w 1 1 • y) := by sorry
