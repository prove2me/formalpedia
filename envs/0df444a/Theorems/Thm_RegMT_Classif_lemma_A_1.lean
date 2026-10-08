-- Prove2me | Theorems.Thm_RegMT_Classif_lemma_A_1
-- name    : RegMT.Classif.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:13.006855+00:00
-- url     : https://prove2.me/theorems/02401912-fc12-4876-a4d4-8f13106e1354
-- title:
--   Lemma A.1, p. 28 — robust reformulation for the label metric
-- statement:
--   Let $N\ge1$ and let $(\hat x_i,\hat y_i)$ be samples in a finite-dimensional normed feature space with binary labels. The transport cost is $d((x,y),(x',y'))=\|x-x'\|+\kappa\mathbf1_{y\ne y'}$, where $\kappa>0$. Let $I$ be a measurable, nonnegative function bounded above by a Lipschitz continuous function. For $\rho>0$,
--   $$\sup_{Q\in\mathbb B_\rho(\hat P_N)}\mathbb E^Q[I(\xi)]=\inf_{\lambda\ge0}\left\{\lambda\rho+\frac1N\sum_{i=1}^N\sup_{\xi}\bigl(I(\xi)-\lambda d(\xi,\hat\xi_i)\bigr)\right\}.$$
--   This is the transport-duality step used to replace an optimization over distributions by one over a scalar transport price.
--
--   **Formalization Note** The paper's proof states strong duality for $\rho>0$; that restriction is explicit here. Nonnegativity is the standing loss convention of §2.1 and permits lower Lebesgue integrals in $[0,\infty]$. The inner supremum is taken after truncating each candidate at zero; the candidate at $\hat\xi_i$ already equals $I(\hat\xi_i)\ge0$, so the supremum is unchanged.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, pp. 28–29, Lemma A.1, (43), proof

import Mathlib
import Definitions.Def_RegMT_Classif_Model

open MeasureTheory
open scoped ENNReal

namespace RegMT.Classif

open DRLogReg.Reformulation

/-- Lemma A.1, p. 28, specialized to the label-switching metric (16). The proof on
p. 29 invokes strong duality for a strictly positive radius. -/
theorem lemma_A_1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {N : ℕ} (hN : 0 < N) (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (I : V × Bool → ℝ)
    (hI : Measurable I) (hI0 : ∀ ξ, 0 ≤ I ξ)
    (hmajor : ∃ K : ℝ, 0 ≤ K ∧ ∃ g : V × Bool → ℝ,
      (∀ ξ ξ', |g ξ - g ξ'| ≤ K * featureLabelDist κ ξ ξ') ∧
      ∀ ξ, I ξ ≤ g ξ) :
    (⨆ Q ∈ wassersteinBall κ ρ (empirical xhat yhat),
      ∫⁻ ξ, ENNReal.ofReal (I ξ) ∂Q) =
    ⨅ (lam : ℝ) (_ : 0 ≤ lam),
      ENNReal.ofReal (lam * ρ) +
        (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N,
          ⨆ ξ : V × Bool, ENNReal.ofReal
            (I ξ - lam * featureLabelDist κ ξ (xhat i, yhat i)) := by sorry

end RegMT.Classif
