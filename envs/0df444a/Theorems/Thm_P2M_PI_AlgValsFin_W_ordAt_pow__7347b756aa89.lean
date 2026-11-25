-- Prove2me | Theorems.Thm_P2M_PI_AlgValsFin_W_ordAt_pow__7347b756aa89
-- name    : P2M_PI_AlgValsFin_W_ordAt_pow__7347b756aa89
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:39.188019+00:00
-- url     : https://prove2.me/theorems/c293d644-f835-46a3-96f9-6d57402cad8c
-- title:
--   P2 M PI Alg Vals Fin W ord At pow  7347b756aa89: P2 M PI Alg Vals Fin W ord At pow  7347b756aa89
-- statement:
--   The P2 M PI Alg Vals Fin W ord At pow  7347b756aa89 construction uses the P2 M PI Alg Vals Fin W ord At pow  7347b756aa89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/OrdFEqOfClassOf.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/OrdFEqOfClassOf.lean#L27-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem P2M_PI_AlgValsFin_W_ordAt_pow__7347b756aa89 (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) (n : ℕ) :
    ordAt L w (a ^ n) = n * ordAt L w a := by sorry

alias «PI».«AlgValsFin».«W».«ordAt_pow'» := P2M_PI_AlgValsFin_W_ordAt_pow__7347b756aa89
