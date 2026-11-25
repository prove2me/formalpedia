-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_ordAt_eU
-- name    : PI.AlgValsFin.W.ordAt_eU
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:13:22.316309+00:00
-- url     : https://prove2.me/theorems/fcdb28fb-9b00-4e69-867e-cd63535e5a56
-- title:
--   W: ord At e U
-- statement:
--   The W construction uses the ord At e U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/OrdFEqOfClassOf.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/OrdFEqOfClassOf.lean#L20-L25

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

theorem PI.AlgValsFin.W.ordAt_eU (v w : HeightOneSpectrum (𝓞 L)) [Decidable (w = v)] :
    ordAt L w (eU v) = if w = v then 1 else 0 := by sorry
