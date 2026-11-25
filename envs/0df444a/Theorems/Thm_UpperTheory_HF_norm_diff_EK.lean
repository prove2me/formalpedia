-- Prove2me | Theorems.Thm_UpperTheory_HF_norm_diff_EK
-- name    : UpperTheory.HF.norm_diff_EK
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:12:20.595809+00:00
-- url     : https://prove2.me/theorems/68165b5a-a45d-5c38-80d3-a21225e09732
-- title:
--   HF: norm diff EK
-- statement:
--   The HF construction uses the norm diff EK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/NormDiffEK.lean#L15-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/NormDiffEK.lean#L15-L50

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiscrK
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_NormDiffEK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.norm_diff_EK :
    ∀ {φ : Frame} (H : HostAx φ), absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) * H.d ^ (2 * φ.ord) = (discr H.E).natAbs ∧ Real.log (absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E))) = 2 * (2 * φ.ord) * (Real.log H.rd - 1 / 2 * Real.log H.d) ∧ ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → absNorm 𝔟 ^ 2 = absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) ∧ Real.log (absNorm 𝔟) = (2 * φ.ord) * (Real.log H.rd - 1 / 2 * Real.log H.d) := by sorry
