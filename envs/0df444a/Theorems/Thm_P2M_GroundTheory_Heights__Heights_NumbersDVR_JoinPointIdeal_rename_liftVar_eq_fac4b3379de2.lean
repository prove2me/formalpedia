-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_rename_liftVar_eq_fac4b3379de2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_rename_liftVar_eq_fac4b3379de2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:00.36588+00:00
-- url     : https://prove2.me/theorems/4a78b525-ff49-470c-8cd1-6b707469b9c1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Ideal rename lift Var eq fac4b3379de2: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Ideal rename lift Var eq fac4b3379de2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Ideal rename lift Var eq fac4b3379de2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Ideal rename lift Var eq fac4b3379de2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinPointIdeal.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinPointIdeal.lean#L58-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinPointIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinPointIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar joinCoord mcIdeal mcMap)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointIdeal
noncomputable section
variable {K : Type} {ι : K → Type}
variable (R : Type) [CommRing R]
variable (Ω : Type) [Field Ω] [Algebra R Ω]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_rename_liftVar_eq_fac4b3379de2 :
    ((rename (liftVar (ι := ι) ptIdx) : MRing ι R →ₐ[R] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) :
        MRing ι R →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) =
      ((srcEquiv (ι := ι) R).symm : MvPolynomial Unit (MRing ι R) →+* _).comp
        (C : MRing ι R →+* MvPolynomial Unit (MRing ι R)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointIdeal».«rename_liftVar_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_rename_liftVar_eq_fac4b3379de2
