-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_theorem_1_2
-- name    : RandOnlineSetCoverSqrt.LowerBound.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T19:34:35.971404+00:00
-- url     : https://prove2.me/theorems/48091ad1-525e-4456-ad7a-78a6e8f71fa0
-- title:
--   Theorem 1.2 — known-instance randomized Ω(√m) lower bound
-- statement:
--   There are universal constants $c>0$ and $m_0\ge1$ such that the following holds for every integer $m\ge m_0$. Give an arbitrary randomized online algorithm the entire canonical universe $U_m$ and all $m$ distinct unit-cost sets in advance, and also the finite horizon
--
--   $$H=(4q+1)\sum_{j=0}^{r}\binom mj,\qquad k=\lfloor\sqrt m\rfloor,\quad q=\lceil\sqrt m\rceil,\quad r=\lfloor m/32\rfloor.$$
--
--   There is a fixed nonempty request sequence $I$ of length $H$, chosen independently of the algorithm's coins, with actual offline minimum $1\le\operatorname{OPT}(I)\le k$ such that both
--
--   $$\mathbb E_R[\operatorname{cost}(I)]\ge(1-e^{-q/4})r,$$
--   $$\mathbb E_R[\operatorname{cost}(I)]\ge c\sqrt m\,\operatorname{OPT}(I).$$
--
--   The expectation is over the algorithm alone. Its decisions may use the full incidence history, retain arbitrary memory, use arbitrarily correlated random coins with real probabilities, and buy any number of sets at each arrival. An incidence label is the full element identity on this fixed known system, so this includes all known-instance algorithms. There is no running-time or memory restriction, no additive competitive allowance and no square-only restriction on $m$.
--
--   Since this one fixed set system is hard for every algorithm, the statement gives the source's lower bound for the general known-instance online set-cover problem. Requests may repeat; $|U_m|=2^m-1$ is distinct from the horizon. The optimum is computed from feasible covers by the published model, rather than supplied as a hypothesis.
--
--   Differences from the source:
--   - generalization: a worst-input Ω(√m) bound for arbitrary known-instance algorithms → the fixed canonical known system with an announced common horizon and the exact quantitative bounds from the proof; reason: a hard witness on this fixed system proves the general lower bound even with horizon information; terminal universal-incidence padding preserves the offline bound and cannot lower purchases
--   - encoding: arbitrary randomized online strategies and an oblivious finite input → PMFs over all valid finite decision tables, with one instance outside the finite-sum expectation; reason: finite-horizon decision tables are a pushforward of arbitrary random coins with no resource restriction; the full known system is fixed and its incidence labels are element identities; pre-request purchases can be delayed to the first request
--   - encoding: positive actual minimum cover and multiplicative competitive ratio → the imported finite optimum, explicit positivity and the multiplied real inequality; reason: every incidence is nonempty and the horizon is positive, so the optimum is finite and at least one; no target inequality is assumed
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Theorem 1.2, printed p. 2 / PDF p. 3; repeated statement and quantitative proof, printed p. 11 / PDF p. 12; Definition 2.1, printed p. 6 / PDF p. 7

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates

namespace RandOnlineSetCoverSqrt.LowerBound

/-- Theorem 1.2, printed p. 2 / PDF p. 3, with the quantitative guarantee in its
proof on printed p. 11 / PDF p. 12. Every decision table is allowed on the complete
publicly known universe Element m; its incidence is exactly its element identity.
Horizon information is supplied before the coins are drawn. The witness I is fixed
outside the expectation, so the adversary is oblivious. -/
theorem theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ R : RandOnlineSetCover.InfoLB.RandAlg m (horizon m),
      ∃ I : RandOnlineSetCover.InfoLB.Instance m (horizon m),
        0 < horizon m ∧
        1 ≤ RandOnlineSetCover.InfoLB.Opt I ∧
        RandOnlineSetCover.InfoLB.Opt I ≤ kParam m ∧
        (1 - Real.exp (-(qParam m : ℝ) / 4)) * (rParam m : ℝ) ≤
          RandOnlineSetCover.InfoLB.expectedCost R I ∧
        c * Real.sqrt (m : ℝ) * (RandOnlineSetCover.InfoLB.Opt I : ℝ) ≤
          RandOnlineSetCover.InfoLB.expectedCost R I := by sorry

end RandOnlineSetCoverSqrt.LowerBound
