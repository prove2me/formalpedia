-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_secIdeal_f302b2e73333
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_secIdeal_f302b2e73333
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:46.520799+00:00
-- url     : https://prove2.me/theorems/cc5550e5-4b99-4683-8fd4-2d679b98d4d9
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain map sec Ideal f302b2e73333: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain map sec Ideal f302b2e73333
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain map sec Ideal f302b2e73333 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain map sec Ideal f302b2e73333 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L260-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L260-L286

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_secIdeal_f302b2e73333 (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
        (X : Par e n → MvPolynomial (Par e n) k)).map
        (MvPolynomial.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n))) =
      secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«map_secIdeal» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_secIdeal_f302b2e73333
