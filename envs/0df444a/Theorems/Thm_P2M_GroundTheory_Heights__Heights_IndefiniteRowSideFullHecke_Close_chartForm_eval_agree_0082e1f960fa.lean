-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForm_eval_agree_0082e1f960fa
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForm_eval_agree_0082e1f960fa
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:47.061803+00:00
-- url     : https://prove2.me/theorems/ad8a44d0-1b50-4b8c-8110-b430eb292bbf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Form eval agree 0082e1f960fa: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Form eval ag
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Form eval agree 0082e1f960fa construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Form eval agree 0082e1f960fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartFormEvalAgree.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartFormEvalAgree.lean#L14-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartFormEvalAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForm_eval_agree_0082e1f960fa (P : ArithVariety n) (A A' : HermLine n) (hdeg : A'.deg = A.deg)
    (hmet : ∀ z ∈ P.points ℂ, A'.metric z = A.metric z)
    (h : ∀ s : IntegralSection P A'.deg,
      (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
          (e e' : MvPolynomial (Coord n) ℤ),
        IsChartForm P A'.deg s.num s.den c d e → IsChartForm P A'.deg s.num s.den c' d' e' →
        (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
          ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A'.metric z) =
            ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A'.metric z)) ∧
        ∃ C : ℝ, s.SupNormLE A' C)
    (s : IntegralSection P A.deg) :
    (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
        (e e' : MvPolynomial (Coord n) ℤ),
      IsChartForm P A.deg s.num s.den c d e → IsChartForm P A.deg s.num s.den c' d' e' →
      (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
        ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z) =
          ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A.metric z)) ∧
      ∃ C : ℝ, s.SupNormLE A C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«chartForm_eval_agree» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForm_eval_agree_0082e1f960fa
