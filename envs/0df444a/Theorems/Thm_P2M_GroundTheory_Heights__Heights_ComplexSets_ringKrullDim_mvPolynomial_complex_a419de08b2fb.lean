-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ringKrullDim_mvPolynomial_complex_a419de08b2fb
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_ringKrullDim_mvPolynomial_complex_a419de08b2fb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:55.93001+00:00
-- url     : https://prove2.me/theorems/6613bc76-ec68-4151-863b-f59d21d2dfc5
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets ring Krull Dim mv Polynomial complex a419de08b2fb: P2 M Ground Theory Heights  Heights Complex Sets ring Krull Dim mv Polynomial complex a419de08b2fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets ring Krull Dim mv Polynomial complex a419de08b2fb construction uses the P2 M Ground Theory Heights  Heights Complex Sets ring Krull Dim mv Polynomial complex a419de08b2fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjHomInjective.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjHomInjective.lean#L9-L12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_ringKrullDim_mvPolynomial_complex_a419de08b2fb (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) ℂ) = d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«ringKrullDim_mvPolynomial_complex» := P2M_GroundTheory_Heights__Heights_ComplexSets_ringKrullDim_mvPolynomial_complex_a419de08b2fb
