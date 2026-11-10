-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8
-- name    : PrivateAgnosticHalfspace.Gaussian.lemma_B_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:38.042249+00:00
-- url     : https://prove2.me/theorems/07ffd957-4f4c-43e0-99d2-c32878df4aa7
-- title:
--   Lemma B.8 — complete Gaussian Hermite basis
-- statement:
--   Write $h_m=\mathrm{He}_m/\sqrt{m!}$ for the normalized probabilists’ Hermite polynomials, and $h_\kappa(x)=\prod_i h_{\kappa_i}(x_i)$ for a natural multi-index $\kappa$. Their defining generating series converges for every real $x,t$:
--   $$
--   e^{tx-t^2/2}=\sum_{m\ge0}h_m(x)\frac{t^m}{\sqrt{m!}}.
--   $$
--   For $\mu=N(0,I_d)$, the family $(h_\kappa)_{\kappa\in\mathbb N_0^d}$ is a complete orthonormal basis of $L^2(\mu)$. For every $p\ge0$, its degree-at-most-$p$ subfamily is an orthonormal basis of all polynomial functions of total degree at most $p$, and
--   $$
--   \dim\mathcal P_p=\binom{d+p}{p}=D_p.
--   $$
--   This identifies both the infinite Gaussian Hilbert-space expansion and each finite coefficient space used by the learner.
--
--   Differences from the source:
--   - encoding: a complete basis of L² and its finite polynomial cutoff → a HilbertBasis with almost-everywhere representatives, explicit finite orthonormal integrals, a pointwise polynomial span identity and the cutoff cardinality; reason: Lp identifies almost-everywhere equal functions; integrability and both infinite completeness and finite spanning are retained
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 22, Lemma B.8; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

theorem lemma_B_8 (d : ℕ) :
    (∀ x t : ℝ, HasSum
      (fun m : ℕ => AMPLowDeg.RankOne.hermNorm m x * t ^ m / Real.sqrt (m.factorial))
      (Real.exp (t * x - t ^ 2 / 2))) ∧
    (∀ κ : Fin d → ℕ, MemLp (hermite d κ) 2 (gaussian d)) ∧
    (∃ b : HilbertBasis (Fin d → ℕ) ℝ (Lp ℝ 2 (gaussian d)),
      ∀ κ, (fun x => (b κ) x) =ᵐ[gaussian d] hermite d κ) ∧
    (∀ p, polynomialFunctions d p = Set.range (polynomialPredictor d p) ∧
      Fintype.card (Index d p) = featureDimension d p ∧
      (∀ κ ξ : Index d p,
        Integrable (fun x => hermite d (fun i => (κ.val i).val) x *
          hermite d (fun i => (ξ.val i).val) x) (gaussian d) ∧
        (∫ x, hermite d (fun i => (κ.val i).val) x *
          hermite d (fun i => (ξ.val i).val) x ∂gaussian d) = if κ = ξ then 1 else 0)) := by sorry

end PrivateAgnosticHalfspace.Gaussian
