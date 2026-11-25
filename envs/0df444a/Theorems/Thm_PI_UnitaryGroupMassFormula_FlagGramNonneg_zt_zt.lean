-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt_zt
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.zt_zt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:45.34588+00:00
-- url     : https://prove2.me/theorems/c2aa3d5a-0e6d-48ba-b03a-a4676b0e2bc8
-- title:
--   Flag Gram Nonneg: zt zt
-- statement:
--   The Flag Gram Nonneg construction uses the zt zt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L92-L100

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

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.zt_zt (hS : hT.IsSymm) (he : ∀ a b, hT (e a) (e b) = 0) (hez : ∀ a, hT (e a) z = 0) :
    hT (zt hT e e' z) (zt hT e e' z) = hT z z := by sorry
