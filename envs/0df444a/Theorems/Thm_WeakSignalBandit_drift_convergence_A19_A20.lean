-- Prove2me | Theorems.Thm_WeakSignalBandit_drift_convergence_A19_A20
-- name    : WeakSignalBandit.drift_convergence_A19_A20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:31.852295+00:00
-- url     : https://prove2.me/theorems/8084ba81-1d71-4715-b86f-701b1e078288
-- title:
--   (A.19)–(A.20), p.34 — the untruncated drift $\tilde b^n$ of $K^n$ converges to $b=(\psi_k,\ \psi_k\mu_k)$ uniformly on compacts
-- statement:
--   Let $P^n_k$ be probability distributions on $\mathbb R$ with finite means $\mu^n_k$ such that $\sqrt n\,\mu^n_k\to\mu_k$ for every arm $k$ (2.9), let $\psi^n$ be functions with values in $\Delta^K$ that form a convergent sequence with limit $\psi$ (Definition 4), and let $K^n=n\Pi^n$ with $\Pi^n$ the kernel (A.14). Then for every $R>0$ and every coordinate $j\in I_Q\cup I_S$,
--   $$\tilde b^n_j(z)=\int(z'_j-z_j)\,K^n(z,dz')\ \xrightarrow{n\to\infty}\ b_j(z)=\begin{cases}\psi_k(z),&j=k\in I_Q,\\ \psi_k(z)\mu_k,&j=k\in I_S,\end{cases}$$
--   uniformly over $z\in D=[0,1]^K\times\mathbb R^K$ with $|z|\le R$.
--
--   Together with (A.21)–(A.25) and (A.18) this verifies the hypotheses (A.11)–(A.13) of Lemma 12 for the bandit's kernel.
--
--   Differences from the source:
--   - generalization: the setting of Theorem 1 (fourth moments bounded, variances converging, ψ Lipschitz, ψⁿ measurable) → finite first moments, √n μⁿ_k → μ_k, ψⁿ Δ^K-valued and convergent; reason: the drift computation uses only these; the setting of Theorem 1 satisfies them
--   - reading: uniformly over the compact set {z : |z| ≤ R} → uniformly over D ∩ {|z| ≤ R}, D = [0,1]^K × ℝ^K; reason: ψ, hence the limit b and a, is defined only on D (Definition 4)
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (A.19)–(A.20) p.34; uniformity over {z : |z| ≤ R}, p.33 and p.35

import Mathlib
import Definitions.Def_WeakSignalBandit_Experiment
import Definitions.Def_WeakSignalBandit_ChainCharacteristics
import Definitions.Def_WeakSignalBandit_BanditKernel
import Definitions.Def_WeakSignalBandit_LimitCoefficients

open MeasureTheory Filter Topology

namespace WeakSignalBandit

/-- **(A.19)–(A.20): convergence of the untruncated drift.** Let `P^n_k` be reward distributions
with finite means satisfying `√n μ^n_k → μ_k` (2.9), let `ψ^n` be sampling functions with values in
`Δ^K` that are convergent with limit `ψ` (Definition 4), and let `K^n = nΠ^n` with `Π^n` the kernel
(A.14). Then for every `R > 0` and every coordinate `j ∈ I_Q ∪ I_S`,
`b̃^n_j(z) = ∫ (z′_j − z_j) K^n(z, dz′) → b_j(z)` uniformly over `z ∈ [0,1]^K × ℝ^K` with
`|z| ≤ R`, where `b_k(z) = ψ_k(z)` for `k ∈ I_Q` and `b_k(z) = ψ_k(z) μ_k` for `k ∈ I_S` (A.15).
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (A.19)–(A.20) p.34 (with "uniformly over the compact set `{z : |z| ≤ R}`",
p.33, and p.35).

**Formalization Note** The uniformity set is `D ∩ {|z| ≤ R}` with `D = [0,1]^K × ℝ^K`, the domain
of the limit sampling function `ψ` (Definition 4). -/
theorem drift_convergence_A19_A20 {K : ℕ} (μ : Fin K → ℝ) (P : ℕ → Fin K → Measure ℝ)
    [∀ n k, IsProbabilityMeasure (P n k)] (hint : ∀ n k, Integrable (fun y : ℝ => y) (P n k))
    (hmean : ∀ k, Tendsto (fun n : ℕ => Real.sqrt n * rewardMean (P n k)) atTop (𝓝 (μ k)))
    (ψn : ℕ → State K → Fin K → ℝ) (hψn : ∀ n z, ψn n z ∈ stdSimplex ℝ (Fin K))
    (ψ : State K → Fin K → ℝ) (hconv : IsConvergentSampling ψn ψ)
    (R : ℝ) (hR : 0 < R) (j : Fin K ⊕ Fin K) :
    TendstoUniformlyOn
      (fun n z => fullDrift (scaledKernel (banditKernel n (P n) (ψn n)) n) z j)
      (fun z => limitDrift μ ψ z j) atTop (domainD ∩ Metric.closedBall 0 R) := by sorry

end WeakSignalBandit
