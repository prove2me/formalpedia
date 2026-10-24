-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_lemma_2
-- name    : ProviderGuarantee.Bound.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:39.880339+00:00
-- url     : https://prove2.me/theorems/2eb9854d-1c1c-4cee-b72d-196c1817b0a0
-- title:
--   Lemma 2, p. 39 (corrected: n0 < n or δ ≤ (n−1)/(2n−1)) — the value of (14) at the vertex with n0 entries γmax is max{δ, (n−1)/(n+n0+(1−δ)(n−n0)−1)}
-- statement:
--   Let $0 < \gamma_{\min} \le \gamma_{\max}$, $\delta = (\gamma_{\max} - \gamma_{\min})/\gamma_{\max}$, and $1 \le n_0 \le n$. Let $\gamma$ be the vertex of $[\gamma_{\min}, \gamma_{\max}]^n$ with $\gamma_i = \gamma_{\max}$ for $i \in \{1, \dots, n_0\}$ and $\gamma_i = \gamma_{\min}$ for $i \in \{n_0 + 1, \dots, n\}$. If $n_0 < n$, or if $\delta \le \frac{n-1}{2n-1}$, then the optimal value of the linear program (14) at $\gamma$ is
--
--   $$\max\left\{\delta, \frac{n-1}{n + n_0 + (1-\delta)(n-n_0) - 1}\right\}.$$
--
--   Lemma 2 evaluates the dual value $f$ at every vertex of the box up to relabelling; combined with the quasiconvexity of $f$ it gives the bound of Theorem 1.
--
--   The printed lemma claims the formula for every $n_0 \in \{1, \dots, n\}$. At $n_0 = n$ all entries equal $\gamma_{\max}$, the program's value is $\frac{n-1}{2n-1}$, and the printed formula is wrong whenever $\delta > \frac{n-1}{2n-1}$. The condition added here excludes exactly those cases; it covers in particular $\gamma_{\min} = \gamma_{\max}$ ($\delta = 0$). Theorem 1 is unaffected, since $\frac{n-1}{2n-1} \le \frac{n-1}{n + (1-\delta)(n-1)}$.
--
--   **Formalization Note** Providers are indexed by `Fin n`, so "the first $n_0$ providers" are the indices $i$ with $i < n_0$ (`vertexProfile n n0 γmin γmax`). The optimal value is `lpValue`.
--
--   Differences from the source:
--   - correction: the formula holds for all n0 ∈ {1, …, n} → it is claimed for 1 ≤ n0 ≤ n with n0 < n or δ ≤ (n−1)/(2n−1); reason: counterexample n = 2, γmin = 1/2, γmax = 1, n0 = 2: γ = (1, 1), δ = 1/2; the value of (14) is 1/3 (attained by x_1 = 1/3, w_21 = w_22 = 1/3 and all other variables 0, and certified by the dual point s = 1/3, λ_ij = 1/3, feasible for (15)), while the printed formula gives max{1/2, 1/3} = 1/2; the proof's primal point uses w_{1,n0+1}, which does not exist when n0 = n
--   - encoding: γ_i = γmax for i ∈ {1, …, n0} → vertexProfile: γ_i = γmax for the indices i < n0 of Fin n; reason: Fin n is 0-based; same profile
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), p. 39, Lemma 2 (proof pp. 39–40)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem lemma_2 (n n0 : ℕ) (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (hn0 : 1 ≤ n0) (hn0n : n0 ≤ n)
    (hcorr : n0 < n ∨ heterogeneity γmin γmax ≤ ((n : ℝ) - 1) / (2 * (n : ℝ) - 1)) :
    lpValue (vertexProfile n n0 γmin γmax) = lemma2Value n n0 (heterogeneity γmin γmax) := by sorry

end ProviderGuarantee.Bound
