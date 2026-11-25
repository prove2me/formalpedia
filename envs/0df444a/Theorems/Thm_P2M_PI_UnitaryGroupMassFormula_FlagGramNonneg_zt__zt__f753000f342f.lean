-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt__zt__f753000f342f
-- name    : P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt__zt__f753000f342f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:40.296323+00:00
-- url     : https://prove2.me/theorems/d56c49f7-64d1-4f2a-8536-ff4044122ac4
-- title:
--   P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt  zt  f753000f342f: P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt  zt  f753000f342f
-- statement:
--   The P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt  zt  f753000f342f construction uses the P2 M PI Unitary Group Mass Formula Flag Gram Nonneg zt  zt  f753000f342f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L102-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L102-L111

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

theorem P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt__zt__f753000f342f (hS : hT.IsSymm) (he' : ∀ a b, hT (e' a) (e' b) = 0)
    (hez' : ∀ a, hT (e' a) z' = 0) :
    hT (zt' hT e e' z') (zt' hT e e' z') = hT z' z' := by sorry

alias «PI».«UnitaryGroupMassFormula».«FlagGramNonneg».«zt'_zt'» := P2M_PI_UnitaryGroupMassFormula_FlagGramNonneg_zt__zt__f753000f342f
