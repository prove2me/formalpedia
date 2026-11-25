-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eventually_eq_interNum_03856f55128c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eventually_eq_interNum_03856f55128c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:09:26.866082+00:00
-- url     : https://prove2.me/theorems/0705b667-22e8-4cc7-b740-9c26152d03e6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman inter Sum eventually eq inter Num 03856f55128c: P2 M Ground Theory Heights  Heights Kleiman inter Sum eventually eq inter Num 03856f55128c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman inter Sum eventually eq inter Num 03856f55128c construction uses the P2 M Ground Theory Heights  Heights Kleiman inter Sum eventually eq inter Num 03856f55128c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L64-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eventually_eq_interNum_03856f55128c (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    {m : ℤ} (h : ∀ᶠ c : ℕ in atTop, interSum pp L c = m) :
    ∀ᶠ c : ℕ in atTop, interSum pp L c = interNum pp L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«interSum_eventually_eq_interNum» := P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eventually_eq_interNum_03856f55128c
