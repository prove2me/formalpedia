-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_3_24
-- name    : RegMT.Classif.Supplement.theorem_3_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:33:57.893282+00:00
-- url     : https://prove2.me/theorems/5e0cd94f-fe3e-4bae-81f8-52dbc4918ad6
-- title:
--   Theorem 3.24 — RKHS lifting bounds
-- statement:
--   Let $H$ be the real RKHS of a kernel on a measurable subset $X$ of a finite-dimensional Euclidean space. Retain the regression output support $Y$ and nonnegative measurable losses. Let $g$ satisfy the complete Assumption 3.22: it is smooth, concave and nonnegative on $[0,\infty)$, $g(0)=0$, $g'\ge1$, and bounds the feature distance by $g$ of the input distance. With $N\ge1$, both optimized learning values obey, for every $\rho\ge0$,
--   $$\hat J_{\rm reg}(\rho)\le\hat J_{H,\rm reg}(\sqrt2\,g(\rho)),\qquad\hat J_{\rm cls}(\rho)\le\hat J_{H,\rm cls}(g(\rho)).$$
--   The regression transport is Euclidean on the joint input-output space; its lifted counterpart is the Hilbert product norm. Classification uses Euclidean feature distance plus a fixed positive label-switching cost. The lifted distributions range over all feature-space inputs, not merely the feature-map image. This result needs no convexity or Lipschitz condition on the loss.
--
--   Differences from the source:
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 16, Theorem 3.24; Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_RKHS

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem theorem_3_24 {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (X : Set V) (hX : MeasurableSet X) (R : RKHSData X H)
    (g : ℝ → ℝ) (hcalm : KernelCalm R g) {N : ℕ} (hN : 0 < N) (x : Fin N → X)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ (Y : Set ℝ), MeasurableSet Y → ∀ y : Fin N → Y,
      ∀ ell : ℝ → ℝ → ℝ, Measurable (Function.uncurry ell) → (∀ s t, 0 ≤ ell s t) →
      (⨅ h : H, originalReg R Y (fun i => (x i : V)) (fun i => (y i : ℝ)) ell ρ h) ≤
        ⨅ h : H, liftedReg (fun i => R.feature (x i)) (fun i => (y i : ℝ)) Y ell
          (Real.sqrt 2 * g ρ) h) ∧
    (∀ y : Fin N → Bool, ∀ ell : ℝ → Bool → ℝ,
      Measurable (Function.uncurry ell) → (∀ s t, 0 ≤ ell s t) → ∀ κ : ℝ, 0 < κ →
      (⨅ h : H, originalClass R (fun i => (x i : V)) y ell κ ρ h) ≤
        ⨅ h : H, liftedClass (fun i => R.feature (x i)) y ell κ (g ρ) h) := by sorry

end RegMT.Classif.Supplement
