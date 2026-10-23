-- Prove2me | Theorems.Thm_RLInference_QValueCLT_eq_23_plugin_clt
-- name    : RLInference.QValueCLT.eq_23_plugin_clt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:13:06.460885+00:00
-- url     : https://prove2.me/theorems/52507a5c-5e81-4368-80c9-2f0d57230f74
-- title:
--   (23), p. 35 — √n([μ̂_{R,n}, P̂_n] − [μ_R, P]) ⇒ N(0, Σ_{R,P}) with Σ_{R,P} of (8)
-- statement:
--   In the setting of (22), with $w$ the stationary distribution of $\tilde P^\pi$, the plug-in parameter vector is asymptotically normal:
--
--   $$\sqrt n\big([\hat\mu_{R,n},\hat P_n]-[\mu_R,P]\big)\;\Rightarrow\;\mathcal N(0,\Sigma_{R,P})\qquad(n\to\infty).$$
--
--   Here $[\cdot,\cdot]$ stacks the $N=|\mathcal S||\mathcal A|$ mean rewards and the $N|\mathcal S|$ transition probabilities into one vector, and by (8)
--
--   $$\Sigma_{R,P}=\begin{pmatrix}W^{-1}D_R&0\\0&D_P\end{pmatrix}.$$
--
--   Here $W^{-1}D_R=\operatorname{diag}(\sigma^2_R(s,a)/w(s,a))$, and $D_P$ is block diagonal with the block of the pair $(s,a)$ equal to $\Sigma_{P_{s,a}}/w(s,a)$, where $\Sigma_{P_{s,a}}$ is the multinomial covariance (4).
--
--   This joint central limit theorem is the probabilistic input of the delta method that proves Theorem 1. The paper obtains it from Slutsky's theorem and Proposition 3 of Trevezas and Limnios (2009).
--
--   **Formalization Note.** The vector lives in `EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S))`, and the limit is Mathlib's `multivariateGaussian 0 Σ_{R,P}`. Convergence in distribution is `TendstoInDistribution` under the chain law, for an arbitrary initial state law. Assumption 3 is irreducibility only; aperiodicity is not assumed.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, p. 35, App. A.1, display (23); Σ_{R,P} from (8), p. 12

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting
open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace RLInference.QValueCLT

theorem eq_23_plugin_clt {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (u0 : S × A → ℝ) (p0 : S × A → S → ℝ)
    (hp0_nonneg : ∀ x k, 0 ≤ p0 x k) (hp0_sum : ∀ x, ∑ k, p0 x k = 1)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y)
    (ν₀ : PMF S) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (WithLp.toLp 2 (fun i => Real.sqrt n * (thetaHat u0 p0 n ω i - theta R P i)) :
          EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S))))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (multivariateGaussian 0 (SigmaRP (Pmat P) (sigma2R R) w)) := by sorry

end RLInference.QValueCLT
