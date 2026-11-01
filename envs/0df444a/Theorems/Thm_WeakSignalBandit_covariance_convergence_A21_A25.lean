-- Prove2me | Theorems.Thm_WeakSignalBandit_covariance_convergence_A21_A25
-- name    : WeakSignalBandit.covariance_convergence_A21_A25
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:34.078651+00:00
-- url     : https://prove2.me/theorems/b014b559-bb8a-4b70-b4d7-da70e6995218
-- title:
--   (A.21)–(A.25), pp.34–35 — the untruncated covariance $\tilde a^n$ of $K^n$ converges to $a=\mathrm{diag}_{I_S}(\psi_k\sigma_k^2)$ uniformly on compacts
-- statement:
--   Let $P^n_k$ be probability distributions on $\mathbb R$ with finite second moments in the weak signal regime with parameters $\mu,\sigma$ ($\sqrt n\,\mu^n_k\to\mu_k$, $(\sigma^n_k)^2\to\sigma_k^2$), let $\psi^n$ be functions with values in $\Delta^K$ forming a convergent sequence with limit $\psi$ (Definition 4), and let $K^n=n\Pi^n$ with $\Pi^n$ the kernel (A.14). Then for every $R>0$ and all coordinates $i,j$ of $\mathbb R^{2K}$,
--   $$\tilde a^n_{i,j}(z)=\int(z'_i-z_i)(z'_j-z_j)\,K^n(z,dz')\ \xrightarrow{n\to\infty}\ a_{i,j}(z)=\begin{cases}\psi_k(z)\sigma_k^2,&i=j=k\in I_S,\\0,&\text{otherwise},\end{cases}$$
--   uniformly over $z\in D=[0,1]^K\times\mathbb R^K$ with $|z|\le R$.
--
--   The five cases of the page — two different $Q$-coordinates (A.21), the same $Q$-coordinate (A.22), a mixed pair (A.23), two different $S$-coordinates (A.24) and the same $S$-coordinate (A.25) — are all covered.
--
--   Differences from the source:
--   - generalization: the setting of Theorem 1 (fourth moments bounded, ψ Lipschitz, ψⁿ measurable) → finite second moments, weak signal regime, ψⁿ Δ^K-valued and convergent; reason: the covariance computation uses only these; the setting of Theorem 1 satisfies them
--   - reading: uniformly over the compact set {z : |z| ≤ R} → uniformly over D ∩ {|z| ≤ R}, D = [0,1]^K × ℝ^K; reason: ψ, hence the limit b and a, is defined only on D (Definition 4)
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (A.21)–(A.25) pp.34–35; uniformity over {z : |z| ≤ R}, p.33 and p.35

import Mathlib
import Definitions.Def_WeakSignalBandit_Experiment
import Definitions.Def_WeakSignalBandit_ChainCharacteristics
import Definitions.Def_WeakSignalBandit_BanditKernel
import Definitions.Def_WeakSignalBandit_LimitCoefficients

open MeasureTheory Filter Topology

namespace WeakSignalBandit

/-- **(A.21)–(A.25): convergence of the untruncated covariance.** Let `P^n_k` be reward
distributions with finite second moments in the weak signal regime with parameters `μ, σ` (2.9), let
`ψ^n` be sampling functions with values in `Δ^K` that are convergent with limit `ψ` (Definition 4),
and let `K^n = nΠ^n` with `Π^n` the kernel (A.14). Then for every `R > 0` and all coordinates
`i, j` of `ℝ^{2K}`, `ã^n_{i,j}(z) = ∫ (z′_i − z_i)(z′_j − z_j) K^n(z, dz′) → a_{i,j}(z)` uniformly
over `z ∈ [0,1]^K × ℝ^K` with `|z| ≤ R`, where `a_{k,l}(z) = ψ_k(z) σ_k²` if `k = l ∈ I_S` and `0`
otherwise (A.17).
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (A.21)–(A.25) pp.34–35 (with "uniformly over the compact set `{z : |z| ≤ R}`",
p.33, and p.35).

**Formalization Note** The uniformity set is `D ∩ {|z| ≤ R}` with `D = [0,1]^K × ℝ^K`, the domain
of the limit sampling function `ψ` (Definition 4). -/
theorem covariance_convergence_A21_A25 {K : ℕ} (μ σ : Fin K → ℝ) (P : ℕ → Fin K → Measure ℝ)
    [∀ n k, IsProbabilityMeasure (P n k)]
    (hint : ∀ n k, Integrable (fun y : ℝ => y ^ 2) (P n k))
    (hweak : IsWeakSignal P μ σ)
    (ψn : ℕ → State K → Fin K → ℝ) (hψn : ∀ n z, ψn n z ∈ stdSimplex ℝ (Fin K))
    (ψ : State K → Fin K → ℝ) (hconv : IsConvergentSampling ψn ψ)
    (R : ℝ) (hR : 0 < R) (i j : Fin K ⊕ Fin K) :
    TendstoUniformlyOn
      (fun n z => fullDiff (scaledKernel (banditKernel n (P n) (ψn n)) n) z i j)
      (fun z => limitDiff σ ψ z i j) atTop (domainD ∩ Metric.closedBall 0 R) := by sorry

end WeakSignalBandit
