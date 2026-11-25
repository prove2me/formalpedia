-- Prove2me | Theorems.Thm_TangentialLaplacianBound
-- name    : TangentialLaplacianBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:35.905938+00:00
-- url     : https://prove2.me/theorems/6ce38401-4062-4111-b9a2-eedf73d4f700
-- title:
--   Tangential Laplacian Bound: Tangential Laplacian Bound
-- statement:
--   R1: at the maximizer `v₀` of `F(θ₀, ·)` on the unit sphere of `e`-perp, the
--   gradient has no component orthogonal to the plane `span{e, v₀}`, each such
--   second derivative is bounded, and summing the adapted orthonormal frame bounds
--   the Laplacian. No spherical Laplacian is used.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TangentialLaplacianBound.lean#L17-L244
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TangentialLaplacianBound.lean#L17-L244

module
public import Definitions.Def_PHarmonicPoly_FrameHessian
public import Definitions.Def_PHarmonicPoly_MvPolyContDiff
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_AdaptedPlanarFrame
public import Definitions.Def_PHarmonicPoly_SecondDerivAtMaxNonpos
public import Definitions.Def_PHarmonicPoly_TangentialLaplacianBound
public import Theorems.Thm_AdaptedPlanarFrame
public import Theorems.Thm_FrameHessian
public import Theorems.Thm_MvPolyContDiff
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner
public import Theorems.Thm_SecondDerivAtMaxNonpos

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem TangentialLaplacianBound {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m)
    {P : MvPolynomial (Fin n) ℝ} (hhom : P.IsHomogeneous m)
    {e v₀ : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hv : ‖v₀‖ = 1)
    (hev : inner ℝ e v₀ = (0 : ℝ))
    (hv0max : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) →
      MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
          EuclideanSpace ℝ (Fin n)) i) P
        ≤ MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ :
          EuclideanSpace ℝ (Fin n)) i) P) :
    (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → inner ℝ e w = (0 : ℝ) →
        inner ℝ v₀ w = (0 : ℝ) →
        inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => y i) P)
          (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) w = (0 : ℝ))
      ∧ (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → inner ℝ e w = (0 : ℝ) →
          inner ℝ v₀ w = (0 : ℝ) →
          iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => y i) P)
            (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![w, w]
          ≤ (m : ℝ) * MvPolynomial.eval (fun i =>
                (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ :
                  EuclideanSpace ℝ (Fin n)) i) P
            + deriv (fun s : ℝ => MvPolynomial.eval
                (fun i => (Real.cos s • e + Real.sin s • v₀ :
                  EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m)
              * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m)))
      ∧ Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => y i) P)
          (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)
        ≤ (m : ℝ) * ((m : ℝ) + (n : ℝ) - 2) * MvPolynomial.eval (fun i =>
              (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ :
                EuclideanSpace ℝ (Fin n)) i) P
          + iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
              (fun i => (Real.cos s • e + Real.sin s • v₀ :
                EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m)
          + ((n : ℝ) - 2) * deriv (fun s : ℝ => MvPolynomial.eval
              (fun i => (Real.cos s • e + Real.sin s • v₀ :
                EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m)
            * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m)) := by sorry
