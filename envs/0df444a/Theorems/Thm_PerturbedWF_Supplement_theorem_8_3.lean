-- Prove2me | Theorems.Thm_PerturbedWF_Supplement_theorem_8_3
-- name    : PerturbedWF.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:09:59.518178+00:00
-- url     : https://prove2.me/theorems/1de1c09a-7832-4f99-b595-9f2f8920d134
-- title:
--   Theorem 8.3: weighted paging, $\sum_t\mathbb E\|X_{t-1}-X_t\|\le\rho_k\mathrm{OPT}+C$ with $\rho_k=\ln k+\ln\ln k+1+o(1)$
-- statement:
--   There are numbers $\rho_k$, depending on $k$ only, with
--   $$\rho_k=\ln k+\ln\ln k+1+o(1)\qquad(k\to\infty),$$
--   such that the following holds. For every cache size $k$, every finite set of pages with weights $w_i\ge0$ and every initial cache $X_0$ there is $C>0$, independent of the request sequence, such that every run of the weighted-paging algorithm of §8.2.1 (each $q_i$ drawn independently with the density (8.2) for $\kappa=(k+1)\ln(k+1)$, $v=\mathrm{diag}(w)\,q$, $X_t\in\arg\max_{x\ni r_t}\{\langle v,x\rangle-W_{t-1}(x)\}$) satisfies, for every request sequence $r_1,\ldots,r_T$,
--   $$\sum_{t=1}^T\mathbb E\big[\|X_{t-1}-X_t\|\big]\le\rho_k\,\mathrm{OPT}+C.$$
--   Here $\|\cdot\|$ is the transportation norm of $d(i,j)=w_i+w_j$, i.e. $\|x-y\|=\sum_iw_i|x_i-y_i|$, and OPT is the minimum of the work function (8.1).
--
--   Together with the lower bound of Theorem 8.4 this settles the randomized competitive ratio of weighted paging up to an additive $1+o(1)$.
--
--   **Formalization Note** Expectations are lower integrals under the product law with density (8.2) on $[-1,1]^n$. $\ln\ln k$ is `Real.log (Real.log k)`; only its values for large $k$ matter.
--
--   Differences from the source:
--   - encoding: 'competitive ratio ρ_k = ln k + ln ln k + 1 + o(1)' → ∃ ρ : ℕ → ℝ with ρ_k − (ln k + ln ln k + 1) → 0 as k → ∞, the bound holding with ρ_k for every instance; reason: the o(1) is a limit in k and ρ_k depends on k only, as in the printed statement
--   - encoding: 'for some C > 0 that is independent of the request sequence' → ∃ C > 0 after k, the pages, w and X₀ and before the horizon, the requests and the run; reason: C may depend on the instance, not on the requests
--   - encoding: the algorithm (any X_t ∈ argmax) → every run: every maximizer at every q in the cube (IsKServerRun); reason: the costs depend on X_t only through diag(w)X_t, which is almost surely unique
--   - encoding: E[·] over q_i i.i.d. with density (8.2) → lower Lebesgue integral under expLaw ι κ (Lebesgue measure on the cube with density ∏ρ(q_i)); reason: the costs are nonnegative
--   - encoding: cache size k ∈ ℕ → every k : ℕ; reason: for k = 0 no configuration contains a request, so no run with N ≥ 1 exists; nothing is added
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Theorem 8.3, p.23 (PDF p.24); the algorithm of §8.2.1, p.22 (PDF p.23); the model of §8.1–§8.2, pp.20–21 (PDF pp.21–22)

import Mathlib
import Definitions.Def_PerturbedWF_Supplement_WeightedPaging

namespace PerturbedWF.Supplement

open MeasureTheory Filter Topology

/-- **Theorem 8.3** (p.23, PDF p.24), for the weighted-paging algorithm of §8.2.1 (p.22).
C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…).

The algorithm has competitive ratio `ρ_k = ln k + ln ln k + 1 + o(1)`. More precisely, there are
numbers `ρ_k` (depending on `k` only) with `ρ_k − (ln k + ln ln k + 1) → 0` such that for every
cache size `k`, every set of pages with weights `w_i ≥ 0` and every initial cache `X₀` there is
`C > 0`, independent of the request sequence, such that every run of the algorithm
(`q_i` i.i.d. with density (8.2), `κ = (k + 1) ln(k + 1)`, `v = diag(w) q`) on every request
sequence satisfies `∑_{t=1}^N E‖X_{t−1} − X_t‖ ≤ ρ_k · OPT + C`.

**Formalization Note.** `‖·‖` is the transportation norm of `d(i, j) = w_i + w_j` (`wpDist`),
`OPT` the minimum of the work function (8.1). Expectations are lower integrals under
`expLaw ι κ`. Every maximizer selection is a run (`IsKServerRun`). -/
theorem theorem_8_3 :
    ∃ ρ : ℕ → ℝ,
      Tendsto (fun k : ℕ => ρ k - (Real.log k + Real.log (Real.log k) + 1)) atTop (𝓝 0) ∧
      ∀ (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ), (∀ i, 0 ≤ w i) →
        ∀ X₀ ∈ kConfig ι k, ∃ C : ℝ, 0 < C ∧
          ∀ (N : ℕ) (r : ℕ → ι) (X : ℕ → (ι → ℝ) → (ι → ℝ)),
            IsKServerRun (wpDist w) k X₀ r (wpMatrix w) N X →
            (∑ t ∈ Finset.Icc 1 N, ∫⁻ q, ENNReal.ofReal
                (transNorm (wpDist w) (X (t - 1) q - X t q)) ∂(expLaw ι (wpKappa k))) ≤
              ENNReal.ofReal (ρ k * ksOPT (wpDist w) k X₀ r N + C) := by sorry

end PerturbedWF.Supplement
