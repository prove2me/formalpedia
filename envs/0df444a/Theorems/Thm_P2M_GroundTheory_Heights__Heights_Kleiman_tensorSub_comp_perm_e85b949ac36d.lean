-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_comp_perm_e85b949ac36d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_comp_perm_e85b949ac36d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:03:32.315844+00:00
-- url     : https://prove2.me/theorems/46ba6f6c-91d6-542e-ad25-377177b13d53
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tensor Sub comp perm e85b949ac36d: P2 M Ground Theory Heights  Heights Kleiman tensor Sub comp perm e85b949ac36d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tensor Sub comp perm e85b949ac36d construction uses the P2 M Ground Theory Heights  Heights Kleiman tensor Sub comp perm e85b949ac36d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L28-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/InterSumEventuallyEqInterNum.lean#L28-L47

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_comp_perm_e85b949ac36d {n : ℕ} (L : Fin n → SubSystem S x Ω) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) :
    tensorSub (fun i => L (σ i)) T = tensorSub L (T.map σ.toEmbedding) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«tensorSub_comp_perm» := P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_comp_perm_e85b949ac36d
