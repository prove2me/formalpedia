-- Prove2me | Theorems.Thm_PI_VolStabS_FFHS_card_isom
-- name    : PI.VolStabS.FFHS.card_isom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:14.553948+00:00
-- url     : https://prove2.me/theorems/d8be4627-42f6-4914-aa81-6ff5ed8bac38
-- title:
--   FFHS: card isom
-- statement:
--   The FFHS construction uses the card isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFIn.lean#L68-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFIn.lean#L68-L86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module Polynomial

theorem PI.VolStabS.FFHS.card_isom {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} := by sorry
