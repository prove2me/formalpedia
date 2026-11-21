-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_Supplement_theorem_1_4
-- name    : RandOnlineSetCoverSqrt.LowerBound.Supplement.theorem_1_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T05:13:37.11037+00:00
-- url     : https://prove2.me/theorems/1b832b68-4eff-4773-b9c6-c9630761f499
-- title:
--   Theorem 1.4 — known-instance random-order $\Omega(m^{1/3})$ lower bound
-- statement:
--   There are constants $c>0$ and $m_0$ such that for every $m\ge m_0$ the following holds. Give the online algorithm the whole canonical universe $U_m=\{u_A:\varnothing\ne A\subseteq[m]\}$ with its $m$ unit-cost sets $S_i=\{u_A:i\in A\}$ in advance; there is a number $N\ge1$ of requests, depending only on $m$ and announced to the algorithm, such that for **every** randomized online algorithm $R$ there is a set $E$ of $N$ distinct elements of $U_m$, fixed independently of the algorithm's coins, with $1\le\operatorname{OPT}(E)$ and
--   $$c\,m^{1/3}\,\operatorname{OPT}(E)\ \le\ \mathbb E_{\pi,R}\bigl[|X_N|\bigr]=\frac1{N!}\sum_{\pi}\mathbb E_R\bigl[\operatorname{cost}(E\text{ revealed in order }\pi)\bigr].$$
--   Here $\pi$ is a uniformly random arrival order, independent of $R$'s randomness, and the cost is the number of distinct sets bought. The algorithm may use the full request history, unlimited memory and computation and correlated coins.
--
--   Hence no randomized algorithm for unweighted online set cover in the known-instance random-order model is $o(m^{1/3})$-competitive, even without element copies.
--
--   Differences from the source:
--   - generalization: every randomized algorithm on every known set system (U, S) with a fixed set E of N distinct elements in random order → the fixed canonical known system U_m, a request count N depending only on m and announced to the algorithm, and for every randomized algorithm a set of N distinct elements; reason: a hard input on one fixed known system for every algorithm that even knows N implies the source lower bound
--   - encoding: arbitrary randomized online algorithms in the random-order model → PMFs over the published valid decision tables at horizon N; reason: finite-horizon decision tables are a pushforward of arbitrary coins; table entries on histories with repeated elements never occur on distinct inputs, so requiring feasibility there (e.g. buying all labels) changes no cost; pre-request purchases can be postponed to the first request
--   - encoding: E_{π,A}[|X_N|] with π uniform and independent of A → (1/N!)·Σ_π expectedCost R (I ∘ π); reason: the same product-law expectation over a finite space
--   - encoding: competitive ratio Ω(m^{1/3}) → ∃ c > 0, ∃ m₀, ∀ m ≥ m₀: c·m^{1/3}·OPT(I) ≤ expected cost, with 1 ≤ OPT(I) and real power m^{1/3}; reason: an α-competitive algorithm satisfies E ≤ α·OPT on every input; the witness shows α ≥ c·m^{1/3}
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Theorem 1.4, printed p. 3 / PDF p. 4; restated with proof, printed pp. 13–16 / PDF pp. 14–17; random-order model, printed p. 7 / PDF p. 8

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_RandomOrder

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement

/-- Theorem 1.4, printed p. 3 / PDF p. 4 and printed p. 13 / PDF p. 14 (proof to PDF p. 17),
in the random-order model of printed p. 7 / PDF p. 8. The set system is the canonical known
universe `U_m`; the number `N` of requests is announced to the algorithm; the adversary fixes a
set of `N` distinct elements (`I`, chosen without seeing the coins), revealed in a uniformly
random order independent of the algorithm's randomness. -/
theorem theorem_1_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ N : ℕ, 0 < N ∧
      ∀ R : RandOnlineSetCover.InfoLB.RandAlg m N,
      ∃ I : RandOnlineSetCover.InfoLB.Instance m N,
        DistinctRequests I ∧
        1 ≤ RandOnlineSetCover.InfoLB.Opt I ∧
        c * (m : ℝ) ^ ((1 : ℝ) / 3) * (RandOnlineSetCover.InfoLB.Opt I : ℝ) ≤
          randomOrderExpectedCost R I := by sorry

end RandOnlineSetCoverSqrt.LowerBound.Supplement
