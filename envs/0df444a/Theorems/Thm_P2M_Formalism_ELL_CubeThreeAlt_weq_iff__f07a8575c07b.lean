-- Prove2me | Theorems.Thm_P2M_Formalism_ELL_CubeThreeAlt_weq_iff__f07a8575c07b
-- name    : P2M_Formalism_ELL_CubeThreeAlt_weq_iff__f07a8575c07b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:50.572951+00:00
-- url     : https://prove2.me/theorems/8fd72ef4-42ce-46c6-9d1f-bd47ec3b8278
-- title:
--   P2 M Formalism ELL Cube Three Alt weq iff  f07a8575c07b: P2 M Formalism ELL Cube Three Alt weq iff  f07a8575c07b
-- statement:
--   The P2 M Formalism ELL Cube Three Alt weq iff  f07a8575c07b construction uses the P2 M Formalism ELL Cube Three Alt weq iff  f07a8575c07b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean#L192-L196

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}

theorem P2M_Formalism_ELL_CubeThreeAlt_weq_iff__f07a8575c07b (W : WeierstrassCurve K) (s v : MvPowerSeries σ K) :
    WEqAt W s v ↔ GG W s v = 0 := by sorry

alias «Formalism».«ELL».«CubeThreeAlt».«weq_iff'» := P2M_Formalism_ELL_CubeThreeAlt_weq_iff__f07a8575c07b
