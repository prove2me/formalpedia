-- Prove2me | Theorems.Thm_PI_WAU_B_cls_eq
-- name    : PI.WAU.B.cls_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:11.316159+00:00
-- url     : https://prove2.me/theorems/23f1db57-002d-4fe6-bcd9-99953d57d37a
-- title:
--   B: cls eq
-- statement:
--   The B construction uses the cls eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean#L72-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean#L72-L101

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]

theorem PI.WAU.B.cls_eq {M : ℕ} (hM : 0 < M) {a a' : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (ha' : ∀ v, a' v ∈ v.adicCompletionIntegers F)
    (h : cls M a = cls M a') :
    ∃ b : FiniteAdeleRing (𝓞 F) F, (∀ v, b v ∈ v.adicCompletionIntegers F) ∧
      a - a' = (M : FiniteAdeleRing (𝓞 F) F) * b := by sorry
