-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_rankcut_competitive
-- name    : RankCutFacility.Shifted.rankcut_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:19.690934+00:00
-- url     : https://prove2.me/theorems/078f3b93-df60-4105-a05c-7fe4bc312997
-- title:
--   Theorem 1.1 / Corollary 4.11 — Exact deterministic RankCut guarantee
-- statement:
--   Let $A(\mu)=1+e^{-(1+\mu)}/\mu$ and $g(\mu)=(3+2\mu+\sqrt{(3+2\mu)^2+4})/2$. The exact parameter $\mu_D$ is the unique solution of $A(\mu)=g(\mu)$ in $(0,1]$. Set $\rho_D^*=A(\mu_D)$ and $\delta_D=\mu_D\rho_D^*$. These constants are well-defined and satisfy
--
--   $$
--   1/8\le\mu_D\le1,\qquad 0<\delta_D\le1/2,\qquad \rho_D^*=g(\mu_D).
--   $$
--
--   For every arbitrary metric space with a finite nonempty ordered candidate set and arbitrary positive real opening costs, every known horizon $n\ge1$, and every multiset $U$ of $n$ demand copies, the offline minimum is attained and Algorithm 1 satisfies
--
--   $$
--   \mathbb E_{\pi\text{ uniform}}[\operatorname{ALG}_{\mu_D,\delta_D}(U,\pi)]\le\rho_D^*\operatorname{OPT}(U),\qquad \rho_D^*<\frac{3538}{1000}.
--   $$
--
--   The algorithm uses the exact implicit parameters, full opening fees, fixed candidate tie-breaking and service-time connections. Copies may coincide. This is the stated known competitive guarantee, with no additive term.
--
--   Differences from the source:
--   - encoding: a finite ordered candidate set in an arbitrary metric space → an injective enumeration by Fin m with m > 0, with its usual order; reason: every finite candidate set and fixed total order has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n request copies → an arbitrary map Fin n → M with n > 0; reason: labels distinguish repeated copies for permutations and never enter an online decision
--   - encoding: uniform or conditional permutation expectation → finite arithmetic averages over all permutations or the indicated nonempty fibers; reason: these are exactly the source finite uniform laws; no integration or measurability assumption is needed
--   - encoding: the unique intersection and common value specified by (28), and a true offline minimum → muD is the infimum of the solution set, accompanied by root and uniqueness certificates; attainment of each finite offline minimum is explicit; reason: the statement proves well-posedness rather than assuming an exact-parameter witness or an optimum
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Theorem 1.1, printed p. 1 (PDF p. 3); Corollary 4.11 and equations (27)–(29), printed pp. 15–16 (PDF pp. 17–18)

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem rankcut_competitive :
    (0 < muD ∧ muD ≤ 1 ∧ limitingA muD = balanceG muD ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ 1 → limitingA μ = balanceG μ → μ = muD) ∧
    (1/8 : ℝ) ≤ muD ∧ muD ≤ 1 ∧ 0 < deltaD ∧ deltaD ≤ (1/2 : ℝ) ∧
    rhoD = balanceG muD ∧ deltaD = muD*rhoD ∧
    (∀ {M : Type*} [MetricSpace M] (G : Geometry M) {n : ℕ}, 0 < n →
      ∀ u : Fin n → M,
        (∃ O : Finset (Fin G.m), O.Nonempty ∧ offlineCost G u O = optimum G u) ∧
        uniformAvg (alg G u muD deltaD) ≤ rhoD * optimum G u) ∧
    rhoD < (3538/1000 : ℝ) := by sorry
end RankCutFacility.Shifted
