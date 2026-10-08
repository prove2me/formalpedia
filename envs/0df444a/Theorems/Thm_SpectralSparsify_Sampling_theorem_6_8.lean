-- Prove2me | Theorems.Thm_SpectralSparsify_Sampling_theorem_6_8
-- name    : SpectralSparsify.Sampling.theorem_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:04.385184+00:00
-- url     : https://prove2.me/theorems/6c9eb152-3737-464a-a90b-852413eb7b84
-- title:
--   Theorem 6.8 (Chernoff Bound) — tails (e^ε/(1+ε)^{1+ε})^{μ/β}, and e^{−με²/3β} for ε < 1, for sums of independent [0, β]-valued two-point variables
-- statement:
--   Let $\beta>0$, let $\alpha_1,\dots,\alpha_n\in[0,\beta]$ and $p_1,\dots,p_n\in[0,1]$, and let $X_1,\dots,X_n$ be independent random variables with $X_i=\alpha_i$ with probability $p_i$ and $X_i=0$ with probability $1-p_i$. Let $X=\sum_i X_i$ and $\mu=\mathbf E[X]=\sum_i\alpha_ip_i$. Then for every $\epsilon>0$,
--   $$\Pr[X>(1+\epsilon)\mu]<\Big(\frac{e^\epsilon}{(1+\epsilon)^{1+\epsilon}}\Big)^{\mu/\beta}\quad\text{and}\quad\Pr[X<(1-\epsilon)\mu]<\Big(\frac{e^\epsilon}{(1+\epsilon)^{1+\epsilon}}\Big)^{\mu/\beta},$$
--   and for $\epsilon<1$ both probabilities are at most $e^{-\mu\epsilon^2/3\beta}$.
--
--   The paper cites this bound from Raghavan (1988), who proved it for $\beta=1$; it is used in Lemma 6.7 ($\epsilon<1$ form) and, with $\epsilon=1$, for the edge count (S.2) of Theorem 6.1.
--
--   **Formalization Note** The outcome is the set $T$ of indices with $X_i=\alpha_i$, so $X=\sum_{i\in T}\alpha_i$. The hypotheses $\beta>0$, $\epsilon>0$ and $p_i\in[0,1]$ are implicit in the paper (with $\beta=0$ the exponent $\mu/\beta$ is undefined). The lower tail is stated, as printed, with the upper-tail expression, which is a valid (weaker) bound.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 15, Theorem 6.8 (citing P. Raghavan, J. Comput. Syst. Sci. 37 (1988))

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset

namespace SpectralSparsify.Sampling

/-- Theorem 6.8 (Chernoff Bound; Spielman–Teng, arXiv:0808.4134v3, p. 15, cited from Raghavan 1988).
Let `α₁, …, αₙ ∈ [0, β]` with `β > 0`, and let `X_i` be independent, equal to `α_i` with probability
`p_i ∈ [0, 1]` and to `0` otherwise; `X = ∑ X_i`, `μ = ∑ α_i p_i`. The outcome is the set `T` of
indices with `X_i = α_i`, so `X = ∑_{i ∈ T} α_i`. For `ε > 0`,
`Pr[X > (1+ε)μ] < (e^ε/(1+ε)^{1+ε})^{μ/β}` and `Pr[X < (1-ε)μ] < (e^ε/(1+ε)^{1+ε})^{μ/β}`;
for `ε < 1` both probabilities are at most `e^{-με²/(3β)}`. -/
theorem theorem_6_8 (n : ℕ) (α pr : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (hα : ∀ i, 0 ≤ α i ∧ α i ≤ β) (hpr : ∀ i, 0 ≤ pr i ∧ pr i ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    prob Finset.univ pr (fun T => (1 + ε) * (∑ i, α i * pr i) < ∑ i ∈ T, α i) <
        (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ ((∑ i, α i * pr i) / β) ∧
      prob Finset.univ pr (fun T => ∑ i ∈ T, α i < (1 - ε) * (∑ i, α i * pr i)) <
        (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ ((∑ i, α i * pr i) / β) ∧
      (ε < 1 →
        prob Finset.univ pr (fun T => (1 + ε) * (∑ i, α i * pr i) < ∑ i ∈ T, α i) ≤
            Real.exp (-((∑ i, α i * pr i) * ε ^ 2) / (3 * β)) ∧
          prob Finset.univ pr (fun T => ∑ i ∈ T, α i < (1 - ε) * (∑ i, α i * pr i)) ≤
            Real.exp (-((∑ i, α i * pr i) * ε ^ 2) / (3 * β))) := by sorry

end SpectralSparsify.Sampling
