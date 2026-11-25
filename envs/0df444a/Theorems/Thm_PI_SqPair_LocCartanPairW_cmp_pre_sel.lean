-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_pre_sel
-- name    : PI.SqPair.LocCartanPairW.cmp_pre_sel
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:11.098464+00:00
-- url     : https://prove2.me/theorems/012934e8-97e7-4f12-89c8-94b00cc26448
-- title:
--   Loc Cartan Pair W: cmp pre sel
-- statement:
--   The Loc Cartan Pair W construction uses the cmp pre sel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L162-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L162-L181

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

theorem PI.SqPair.LocCartanPairW.cmp_pre_sel {ι : Type*} [Fintype ι] [DecidableEq ι] (h h₁ g₁ : Matrix ι ι R) (ϖ : R)
    (m a : ℕ) (hh₁ : h = ϖ ^ m • h₁) (hg : h₁ * g₁ = ϖ ^ (2 * a) • (1 : Matrix ι ι R)) (j : ι)
    (x y : ι → R) (hx : x = h₁ *ᵥ Pi.single j 1) (w : Matrix (Fin 2) (Fin 2) R) (α α' s' : R)
    (hα : α = ϖ ^ (2 * a) * α') (hw : w 1 0 = α * s') :
    h *ᵥ (w 0 0 • Pi.single j 1 + (s' * α') • (g₁ *ᵥ y)) = ϖ ^ m • (w 0 0 • x + w 1 0 • y) ∧
      h *ᵥ ((w 0 1 * ϖ ^ (2 * a)) • Pi.single j 1 + w 1 1 • (g₁ *ᵥ y)) =
        (ϖ ^ m * ϖ ^ (2 * a)) • (w 0 1 • x + w 1 1 • y) := by sorry
