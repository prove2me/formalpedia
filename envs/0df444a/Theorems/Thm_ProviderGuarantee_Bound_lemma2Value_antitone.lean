-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_lemma2Value_antitone
-- name    : ProviderGuarantee.Bound.lemma2Value_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:36.711635+00:00
-- url     : https://prove2.me/theorems/d95a6dcc-6c6a-41cc-8896-8df331c14f9e
-- title:
--   Proof of Theorem 1, p. 39 — max{δ, (n−1)/(n+n0+(1−δ)(n−n0)−1)} is non-increasing in n0, and at n0 = 1 it is the bound (5)
-- statement:
--   Let $0 < \gamma_{\min} \le \gamma_{\max}$, $\delta = (\gamma_{\max} - \gamma_{\min})/\gamma_{\max}$, and for $n_0 \in \{1, \dots, n\}$ put
--
--   $$g(n_0) = \max\left\{\delta, \frac{n-1}{n + n_0 + (1-\delta)(n-n_0) - 1}\right\}.$$
--
--   Then $g$ is non-increasing: $g(n_0') \le g(n_0)$ whenever $1 \le n_0 \le n_0' \le n$. Moreover
--
--   $$g(1) = \max\left\{\delta, \frac{n-1}{n + (1-\delta)(n-1)}\right\},$$
--
--   the right-hand side of (5).
--
--   This is the last step of the proof of Theorem 1: among the vertices of the box, the one with a single provider at $\gamma_{\max}$ gives the largest value, and that value is the bound.
--
--   Differences from the source:
--   - reading: 'this is a decreasing function of n0' → non-increasing: g(n0') ≤ g(n0) for 1 ≤ n0 ≤ n0' ≤ n; reason: for δ = 0, or when δ dominates, g is constant, so strict decrease is false; the page uses only that n0 = 1 maximizes g
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), p. 39, proof of Theorem 1

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem lemma2Value_antitone (n : ℕ) (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (n0 n0' : ℕ) (h1 : 1 ≤ n0) (h2 : n0 ≤ n0') (h3 : n0' ≤ n) :
    lemma2Value n n0' (heterogeneity γmin γmax) ≤ lemma2Value n n0 (heterogeneity γmin γmax) ∧
    lemma2Value n 1 (heterogeneity γmin γmax) = lossBound n (heterogeneity γmin γmax) := by sorry

end ProviderGuarantee.Bound
