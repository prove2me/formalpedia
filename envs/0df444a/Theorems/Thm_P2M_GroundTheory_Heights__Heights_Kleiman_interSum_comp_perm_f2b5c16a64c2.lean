-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interSum_comp_perm_f2b5c16a64c2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_interSum_comp_perm_f2b5c16a64c2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:09:23.639156+00:00
-- url     : https://prove2.me/theorems/a908bcc1-97ce-4582-8d69-20bdca4ce535
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman inter Sum comp perm f2b5c16a64c2: P2 M Ground Theory Heights  Heights Kleiman inter Sum comp perm f2b5c16a64c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman inter Sum comp perm f2b5c16a64c2 construction uses the P2 M Ground Theory Heights  Heights Kleiman inter Sum comp perm f2b5c16a64c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L49-L54

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_interSum_comp_perm_f2b5c16a64c2 (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) (c : ℕ) :
    interSum pp (fun i => L (σ i)) c = interSum pp L c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«interSum_comp_perm» := P2M_GroundTheory_Heights__Heights_Kleiman_interSum_comp_perm_f2b5c16a64c2
