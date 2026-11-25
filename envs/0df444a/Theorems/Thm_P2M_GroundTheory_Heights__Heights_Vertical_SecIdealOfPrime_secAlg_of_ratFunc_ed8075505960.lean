-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_secAlg_of_ratFunc_ed8075505960
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_secAlg_of_ratFunc_ed8075505960
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:13.489802+00:00
-- url     : https://prove2.me/theorems/2c50cb84-575c-4264-a166-0472991473c7
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Ideal Of Prime sec Alg of rat Func ed8075505960: P2 M Ground Theory Heights  Heights Vertical Sec Ideal Of Prime sec Alg of rat Func ed8075505960
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Ideal Of Prime sec Alg of rat Func ed8075505960 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Ideal Of Prime sec Alg of rat Func ed8075505960 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecIdealOfPrime.lean#L17-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecIdealOfPrime.lean#L17-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecIdealOfPrime
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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecIdealOfPrime

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_secAlg_of_ratFunc_ed8075505960 {k E : Type} [Field k] [Field E] (n e : ℕ) (φ : k →+* E) (y : Par e n → E)
    (hinj : Function.Injective (eval₂Hom φ y))
    (hsurj : ∀ z : E, ∃ a b, z = eval₂Hom φ y a / eval₂Hom φ y b)
    (Q : Ideal (MvPolynomial (Fin n) k)) (hQF : IsField (GenSec k e Q))
    (hQK : RingHom.ker ((Ideal.Quotient.mk
        (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))).comp
          (MvPolynomial.map (algebraMap k (GenParField k e n)))) = Q) :
    IsField (SecAlg (Q.map (MvPolynomial.map φ)) y) ∧
      RingHom.ker ((Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map φ)) y)).comp
        (MvPolynomial.map φ)) = Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecIdealOfPrime».«secAlg_of_ratFunc» := P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_secAlg_of_ratFunc_ed8075505960
