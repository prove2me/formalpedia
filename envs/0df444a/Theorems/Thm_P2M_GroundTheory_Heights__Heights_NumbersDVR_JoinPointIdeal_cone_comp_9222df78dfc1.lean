-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_cone_comp_9222df78dfc1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_cone_comp_9222df78dfc1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:45.999744+00:00
-- url     : https://prove2.me/theorems/e5ad19d4-5bc4-4294-ace1-e75cd6af7851
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Ideal cone comp 9222df78dfc1: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Ideal cone comp 9222df78dfc1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Ideal cone comp 9222df78dfc1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Ideal cone comp 9222df78dfc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinPointIdeal.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinPointIdeal.lean#L43-L56

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_cone_comp_9222df78dfc1 (y : (Σ k, ι k) → Ω) :
    ((tgtEquiv (K := K) Ω : MvPolynomial (K ⊕ Unit) Ω →+* MvPolynomial Unit (MvPolynomial K Ω))).comp
        ((mcMap R (joinCoord y (ptCoord (Ω := Ω))) :
            MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →ₐ[R] MvPolynomial (K ⊕ Unit) Ω) :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial (K ⊕ Unit) Ω) =
      (MvPolynomial.map ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* _)).comp
        (srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointIdeal».«cone_comp» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_cone_comp_9222df78dfc1
