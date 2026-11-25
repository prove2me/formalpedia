-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenEuler_quotH_subsingleton_5b384063a440
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenEuler_quotH_subsingleton_5b384063a440
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:14.747088+00:00
-- url     : https://prove2.me/theorems/189f28db-5aea-5c0e-ae75-0f2ded9e5642
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Euler quot H subsingleton 5b384063a440: P2 M Ground Theory Heights  Heights Kleiman Restr Len Euler quot H subsingleton 5b384063a440
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Euler quot H subsingleton 5b384063a440 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Euler quot H subsingleton 5b384063a440 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrLenEuler.lean#L53-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PRestrLenEuler.lean#L53-L88

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
set_option maxHeartbeats 1000000

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenEuler_quotH_subsingleton_5b384063a440 (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (i : ℕ)
    (h1 : Subsingleton (F₁.H i)) (h2 : Subsingleton (F₂.H (i + 1))) :
    Subsingleton (SubSystem.quotH F₁ F₂ i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenEuler».«quotH_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenEuler_quotH_subsingleton_5b384063a440
