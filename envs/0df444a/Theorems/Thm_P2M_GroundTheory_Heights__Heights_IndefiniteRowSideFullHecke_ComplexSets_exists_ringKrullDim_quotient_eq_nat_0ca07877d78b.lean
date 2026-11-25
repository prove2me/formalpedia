-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_ringKrullDim_quotient_eq_nat_0ca07877d78b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_ringKrullDim_quotient_eq_nat_0ca07877d78b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:54.450795+00:00
-- url     : https://prove2.me/theorems/63207108-4737-5ea7-ba1f-31e4ca393b1d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists ring Krull Dim quotient eq nat 0ca07877d78b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke C
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists ring Krull Dim quotient eq nat 0ca07877d78b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists ring Krull Dim quotient eq nat 0ca07877d78b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularOffHypersurface.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularOffHypersurface.lean#L12-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_ringKrullDim_quotient_eq_nat_0ca07877d78b {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_ringKrullDim_quotient_eq_nat» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_ringKrullDim_quotient_eq_nat_0ca07877d78b
