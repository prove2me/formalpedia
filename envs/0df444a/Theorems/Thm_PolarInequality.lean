-- Prove2me | Theorems.Thm_PolarInequality
-- name    : PolarInequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:10.929098+00:00
-- url     : https://prove2.me/theorems/65660b62-24a0-4154-a41f-08be8c6d6ffa
-- title:
--   Polar Inequality: Polar Inequality
-- statement:
--   The paper's eq:polar, as an inequality: dividing `E_p(u)(x₀) = 0` by
--   `m^2 |Du(x₀)|^2 = m^4 q` and replacing the Laplacian by the adapted-frame bound
--   makes the right-hand side nonnegative.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/PolarInequality.lean#L14-L188
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/PolarInequality.lean#L14-L188

module
public import Definitions.Def_PHarmonicPoly_TangentialLaplacianBound
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_AdaptedPlanarFrame
public import Definitions.Def_PHarmonicPoly_PolarInequality
public import Theorems.Thm_AdaptedPlanarFrame
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_TangentialLaplacianBound

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial Real

theorem PolarInequality {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) {p : ℝ}
    (hp : (n : ℝ) - 1 / 13 ≤ p)
    {P : MvPolynomial (Fin n) ℝ} (hhom : P.IsHomogeneous m)
    {e v₀ : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hv : ‖v₀‖ = 1)
    (hev : inner ℝ e v₀ = (0 : ℝ))
    (hmax : MvPolynomial.eval (fun i => e i) P = 1)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ 1)
    (hE : EpAlg p P = 0)
    (hv0max : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) →
      MvPolynomial.eval (fun i => (Real.cos (π / m) • e + Real.sin (π / m) • v :
          EuclideanSpace ℝ (Fin n)) i) P
        ≤ MvPolynomial.eval (fun i => (Real.cos (π / m) • e + Real.sin (π / m) • v₀ :
          EuclideanSpace ℝ (Fin n)) i) P)
    (a b c q : ℝ)
    (hadef : MvPolynomial.eval (fun i => (Real.cos (π / m) • e + Real.sin (π / m) • v₀ :
      EuclideanSpace ℝ (Fin n)) i) P = -a)
    (hbdef : deriv (fun s : ℝ => MvPolynomial.eval
      (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (π / m)
        = (m : ℝ) * b)
    (hcdef : iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
      (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (π / m)
        = (m : ℝ) ^ 2 * c)
    (hqdef : q = a ^ 2 + b ^ 2) (hq0 : 0 < q) :
    0 ≤ c - (p - 1 + ((n : ℝ) - p) / m) * a
        + ((n : ℝ) - 2) * (Real.cos (π / m) / (Real.sin (π / m) * m)) * b
        + (p - 2) * (b ^ 2 * (c - a) / q) := by sorry
