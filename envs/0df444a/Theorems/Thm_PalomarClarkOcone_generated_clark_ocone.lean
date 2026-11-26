-- Prove2me | Theorems.Thm_PalomarClarkOcone_generated_clark_ocone
-- name    : PalomarClarkOcone.generated_clark_ocone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:06.113849+00:00
-- url     : https://prove2.me/theorems/d7a68dc8-2356-4e91-ac20-1c23fc5a1f32
-- title:
--   Palomar Clark Ocone: generated clark ocone
-- statement:
--   **Generated-space martingale representation and textbook Clark--Ocone.** There are
--   a time realization of the closed Malliavin derivative and a Brownian Itô
--   isometry such that every terminal `L²` variable has a stochastic-integral
--   representation. For every pair in the closed Malliavin graph, the predictable
--   projection of the derivative has a representative whose time sections are the
--   conditional expectations in the textbook Clark--Ocone identity. The Brownian
--   coordinate directions are total in the Cameron--Martin space, so the displayed
--   generator law determines the continuous time realization.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/ClarkOconeSolution.lean#L262-L374
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/ClarkOconeSolution.lean#L262-L374

import Definitions.Def_Malliavin_BrownianClarkOconeCapstone
import Definitions.Def_ClarkOconeSolution
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real Topology InnerProductSpace
noncomputable section
open PalomarClarkOcone
universe u
set_option maxHeartbeats 800000

theorem PalomarClarkOcone.generated_clark_ocone
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P)
    (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm) :
    ∃ (timeDerivative : Lp (CameronMartin.Space P) 2 P →ₗᵢ[ℝ] TimeProcessL2 P)
        (itoIntegral : PredictableProcessL2 filtration P →L[ℝ] RandomL2 P),
      (∀ h : CameronMartin.Space P,
        (∀ t, ⟪h, CameronMartin.ofDual P (coordinate t)⟫_ℝ = 0) → h = 0) ∧
      (∀ t (G : RandomL2 P),
        (timeDerivative (smulLp (CameronMartin.ofDual P (coordinate t)) G) :
            ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
          fun p ↦ (Set.Ioc 0 t).indicator (1 : ℝ≥0 → ℝ) p.1 * G p.2) ∧
      (∀ U, ‖itoIntegral U‖ = ‖U‖) ∧
      (∀ U, ∫ w, itoIntegral U w ∂P = 0) ∧
      (∀ {a b : ℝ≥0} (_hab : a ≤ b)
          (Z : lpMeas ℝ ℝ (filtration a) 2 P),
        ∃ U : PredictableProcessL2 filtration P,
          (U : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
            (fun p ↦ (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 *
              (Z : W → ℝ) p.2) ∧
          (itoIntegral U : W → ℝ) =ᵐ[P]
            fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) ∧
      (∀ G : RandomL2 P, ∃ U : PredictableProcessL2 filtration P,
        G = expectationL2 G + itoIntegral U) ∧
      ∀ {F : RandomL2 P} {η : Lp (CameronMartin.Space P) 2 P},
        InGraphClosure P F η →
          ∃ G : ℝ≥0 × W → ℝ,
            StronglyMeasurable[filtration.predictable] G ∧
            (predictableProjection filtration (timeDerivative η) :
                ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
            (∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
              (fun w ↦ G (t, w)) =ᵐ[P]
                P[(fun w ↦ (timeDerivative η : ℝ≥0 × W → ℝ) (t, w)) |
                  filtration t]) ∧
            F = expectationL2 F +
              itoIntegral (predictableProjection filtration (timeDerivative η)) := by sorry
