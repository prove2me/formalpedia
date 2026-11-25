-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_locNb
-- name    : PI.AlgValsFin.W.locNb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:08.281434+00:00
-- url     : https://prove2.me/theorems/f280b62c-f5f4-5097-a7b7-dc6831979d6a
-- title:
--   W: loc Nb
-- statement:
--   The W construction uses the loc Nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean#L11-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.locNb (v : HeightOneSpectrum (𝓞 L))
    (s : Set ((v.adicCompletionIntegers L : Set (v.adicCompletion L))))
    (hs : s ∈ 𝓝 (⟨1, (v.adicCompletionIntegers L).one_mem⟩ : (v.adicCompletionIntegers L : Set (v.adicCompletion L)))) :
    ∃ n : ℕ, ∀ y : (v.adicCompletionIntegers L : Set (v.adicCompletion L)),
      Valued.v ((y : v.adicCompletion L) - 1) ≤ exp (-(n : ℤ)) → y ∈ s := by sorry
