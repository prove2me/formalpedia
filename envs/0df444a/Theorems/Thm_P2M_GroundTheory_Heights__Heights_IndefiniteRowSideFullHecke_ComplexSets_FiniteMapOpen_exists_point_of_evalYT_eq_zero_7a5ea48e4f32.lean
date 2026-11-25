-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_exists_point_of_evalYT_eq_zero_7a5ea48e4f32
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_exists_point_of_evalYT_eq_zero_7a5ea48e4f32
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:30.503051+00:00
-- url     : https://prove2.me/theorems/5eb551f0-9ea7-4e86-b219-f6e32e9dfac9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open exists point of eval YT eq zero 7a5ea48e4f32: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open exists point of eval YT eq zero 7a5ea48e4f32 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Finite Map Open exists point of eval YT eq zero 7a5ea48e4f32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteMapOpen.lean#L95-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteMapOpen.lean#L95-L152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_exists_point_of_evalYT_eq_zero_7a5ea48e4f32 (J : Ideal (MvPolynomial (Fin n) ℂ))
    (p : Fin d → MvPolynomial (Fin n) ℂ) (hfin : ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).Finite)
    (L : MvPolynomial (Fin n) ℂ) (μ : Polynomial (MvPolynomial (Fin d) ℂ))
    (hdvd : ∀ F, Polynomial.eval₂ ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom
      (Ideal.Quotient.mk J L) F = 0 → μ ∣ F)
    {y : Fin d → ℂ} {t : ℂ} (hyt : evalYT μ y t = 0) :
    ∃ z ∈ zeroLocus J, (fun i => eval z (p i)) = y ∧ eval z L = t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FiniteMapOpen».«exists_point_of_evalYT_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_exists_point_of_evalYT_eq_zero_7a5ea48e4f32
