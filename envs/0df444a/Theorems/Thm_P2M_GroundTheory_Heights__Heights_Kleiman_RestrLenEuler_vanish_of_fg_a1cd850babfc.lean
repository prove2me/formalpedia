-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenEuler_vanish_of_fg_a1cd850babfc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenEuler_vanish_of_fg_a1cd850babfc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:25.458798+00:00
-- url     : https://prove2.me/theorems/d916d1f0-d413-524a-b031-5053a65d46c1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Euler vanish of fg a1cd850babfc: P2 M Ground Theory Heights  Heights Kleiman Restr Len Euler vanish of fg a1cd850babfc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Euler vanish of fg a1cd850babfc construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Euler vanish of fg a1cd850babfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrLenEuler.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrLenEuler.lean#L36-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AssemblyBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrLenEuler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenEuler
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenEuler_vanish_of_fg_a1cd850babfc (F : SubFamily k x Ω) (hF : ∀ I, (F.sub I).FG) :
    ∃ c₀ : ℤ, ∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton ((F.toSubSystem.twist (twistSys k x c)).H i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenEuler».«vanish_of_fg» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenEuler_vanish_of_fg_a1cd850babfc
