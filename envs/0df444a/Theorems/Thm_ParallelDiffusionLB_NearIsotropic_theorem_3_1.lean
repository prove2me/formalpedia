-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_theorem_3_1
-- name    : ParallelDiffusionLB.NearIsotropic.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:31.611127+00:00
-- url     : https://prove2.me/theorems/8018ca13-4cf5-4129-ad42-50a9db74d542
-- title:
--   Theorem 3.1 — Near-isotropic parallel diffusion round lower bound
-- statement:
--   For every fixed target smoothing $\gamma>0$ and natural polynomial exponents $a,b$, there are $c>0$ and $d_0\ge2$ such that for every $d\ge d_0$, query budget $1\le P\le d^a$ and score accuracy $\varepsilon>0$ with $\varepsilon\ge d^{-b}$, there exists a probability law $\mu$ on finitely many target-oracle pairs. Each pair consists of a nonempty finite set of distinct centers $C_i\subseteq\mathbb R^d$, the equal-weight target
--   $$\pi_i=\frac1{|C_i|}\sum_{y\in C_i}N(y,\gamma^2I_d),$$
--   and a fixed jointly measurable oracle $\hat s_i$ legal at every additional noise level $\sigma>0$. Every target satisfies
--   $$\|E_{\pi_i}X\|\le d^{-10},\qquad\|\operatorname{Cov}(\pi_i)-(1+\gamma^2)I_d\|_{op}\le d^{-10}.$$
--   For every randomized measurable adaptive sampler with any independent seed probability space, at most $P$ queries per round and $R\le c(d/\log d)^{1/3}$ rounds,
--   $$\Pr_{i\sim\mu}\left[d_{TV}(Q_i^A,\pi_i)\ge0.9\right]\ge0.9.$$
--   Here $Q_i^A$ averages over the algorithm's seed for fixed instance $i$; the finite instance law is chosen before the algorithm. The oracle's mean-square error is at most $\varepsilon^2/\sigma^2$ under the true smoothed target for every $\sigma>0$. There is no computational or query-location restriction. This is the full distributional lower bound, including both 0.9 constants, Gaussian-mixture geometry and near-isotropy.
--
--   Differences from the source:
--   - generalization: there is a near-isotropic family for a fixed smoothing constant → for every fixed gamma>0 chosen before dimension; reason: Appendix A fixes arbitrary gamma>0; all constants may depend on it and every source family is an instance
--   - generalization: polynomial query budgets and inverse-polynomial score accuracy fixed in advance → uniformly over P≤d^a and epsilon≥d^(−b) for fixed natural exponents, with no upper bound on epsilon; reason: the public parameter estimates use only polynomial envelopes; for epsilon>1 a legal oracle at accuracy 1 remains legal at accuracy epsilon
--   - generalization: a family of fixed legal oracle maps → the oracles have explicit joint measurability; reason: the constructed finite-mixture oracle has this property, ensuring genuine output probability laws
--   - encoding: at most P queries per round and an independent random seed → P query slots, measurable batch and output maps, and an arbitrary probability seed space; reason: unused slots can be filled with a fixed legal query and ignored; all finite-round measurable algorithms have this representation
--   - reading: O((d/log d)^(1/3)) rounds → at most c(d/log d)^(1/3) rounds for some c>0 fixed before d; reason: Theorem 1.1, §3.3 and the proof of A.1 choose a sufficiently small constant for B and require R<B
--   - encoding: a family of near-isotropic Gaussian mixtures and its instance distribution → a probability law on Fin K with nonempty finite distinct center sets and explicit bounds (17); reason: the proof conditions a finite codebook product law on the event G; Fin K relabels its finite support
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Theorem 3.1; proof p. 12 and (17) p. 19, p. 6

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- Theorem 3.1 (p. 6), with fixed gamma and polynomial budgets made explicit.
The finite instance law is chosen before quantifying over all measurable randomized algorithms. -/
theorem theorem_3_1 (γ : ℝ) (hγ : 0 < γ) (a b : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧
    ∀ d : ℕ, d₀ ≤ d → ∀ P : ℕ, 1 ≤ P → P ≤ d ^ a →
    ∀ ε : ℝ, 0 < ε → (d : ℝ) ^ (-(b : ℤ)) ≤ ε →
    ∃ K : ℕ, 0 < K ∧ ∃ μ : Measure (Fin K), IsProbabilityMeasure μ ∧
    ∃ C : Fin K → Finset (E d), ∃ o : Fin K → Query d → E d,
      (∀ i, (C i).Nonempty ∧
        IsNearIsotropic (mixture (C i) γ) γ ((d : ℝ) ^ (-10 : ℤ)) ∧
        LegalOracle (mixture (C i) γ) ε (o i)) ∧
      ∀ R : ℕ, (R : ℝ) ≤ c * (d / Real.log d : ℝ) ^ (1 / 3 : ℝ) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
        (A : ParallelAlgorithm (Query d) (E d) (E d) Ω P R),
        (9 / 10 : ℝ) ≤ μ.real {i | (9 / 10 : ℝ) ≤
          PolySampIso.tvDist (A.outputLaw ν (o i)) (mixture (C i) γ)} := by sorry

end ParallelDiffusionLB.NearIsotropic
