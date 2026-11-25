-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_yv_zt
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.yv_zt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:15.287118+00:00
-- url     : https://prove2.me/theorems/941ac396-8e82-5da8-89c2-7bb89865f35c
-- title:
--   Flag Gram Nonneg: yv zt
-- statement:
--   The Flag Gram Nonneg construction uses the yv zt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L151-L157

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
variable (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V)

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.yv_zt (hS : hT.IsSymm) (hA : IsUnit (amat hT e e').det) (he : ∀ a b, hT (e a) (e b) = 0)
    (hez : ∀ a, hT (e a) z = 0) (a : Fin r) : hT (yv hT e e' a) (zt hT e e' z) = 0 := by sorry
