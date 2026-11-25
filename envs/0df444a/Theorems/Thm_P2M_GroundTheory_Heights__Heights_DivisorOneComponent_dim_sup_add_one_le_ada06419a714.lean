-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorOneComponent_dim_sup_add_one_le_ada06419a714
-- name    : P2M_GroundTheory_Heights__Heights_DivisorOneComponent_dim_sup_add_one_le_ada06419a714
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:38:41.737882+00:00
-- url     : https://prove2.me/theorems/4192b6b2-efa8-5145-a822-7399ae8e408e
-- title:
--   P2 M Ground Theory Heights  Heights Divisor One Component dim sup add one le ada06419a714: P2 M Ground Theory Heights  Heights Divisor One Component dim sup add one le ada06419a714
-- statement:
--   The P2 M Ground Theory Heights  Heights Divisor One Component dim sup add one le ada06419a714 construction uses the P2 M Ground Theory Heights  Heights Divisor One Component dim sup add one le ada06419a714 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorOneComponent.lean#L46-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorOneComponent.lean#L46-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorOneComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorOneComponent

theorem P2M_GroundTheory_Heights__Heights_DivisorOneComponent_dim_sup_add_one_le_ada06419a714 {n d : ℕ} {J W W' : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime] {u : Fin n → ℂ}
    (hu : linForm u ∉ J) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes)
    (hW' : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) (hne : W ≠ W') :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1 ≤ (d : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DivisorOneComponent».«dim_sup_add_one_le» := P2M_GroundTheory_Heights__Heights_DivisorOneComponent_dim_sup_add_one_le_ada06419a714
