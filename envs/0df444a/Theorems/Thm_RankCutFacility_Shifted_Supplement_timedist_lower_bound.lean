-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_timedist_lower_bound
-- name    : RankCutFacility.Shifted.Supplement.timedist_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:27:54.390397+00:00
-- url     : https://prove2.me/theorems/a04f4648-02d5-4487-88bf-bbd94c8b9efa
-- title:
--   Theorem B.5 — Lower bound $C^*$ for Candidate Marginal TimeDist rules
-- statement:
--   A **Candidate Marginal TimeDist rule** (Definition B.4) is a family of instance-independent functions $g_n:\{2,\dots,n\}\times\mathbb R_{\ge0}\to[0,1]$. At rank 1 it opens a fixed nearest candidate; at rank $t\ge2$, with $\Delta_t=(d(v_t,O_{t-1})-d(v_t,F))^+$, conditional on the complete history it opens a fixed nearest candidate with probability exactly $g_n(t,\Delta_t)$; it then connects to the nearest open facility. Let $\mu^*$ be the unique solution in $(0,1]$ of $\Phi(\mu)=3+2\mu$ and $C^*=\Phi(\mu^*)=3+2\mu^*$; the statement certifies both.
--
--   **Theorem B.5.** For every Candidate Marginal TimeDist rule $G=(g_n)_{n\ge1}$,
--
--   $$\limsup_{n\to\infty}\ \sup_{I:|I|=n}\frac{\mathbb E[\mathrm{ALG}_G(I)]}{\mathrm{OPT}(I)}\ge C^*,$$
--
--   the supremum over unit-cost prescribed-candidate instances with $n$ demand copies and the expectation over the uniform arrival order and the rule's randomness: for every $c<C^*$ and $N_0$ there are $n\ge N_0$ and a finite such instance with $\mathbb E[\mathrm{ALG}_G]>c\cdot\mathrm{OPT}$ under every nearest-candidate tie order. Consequently Candidate Marginal DistCut with $\mu=\mu^*$ is asymptotically optimal in this class: its rule $g_n(t,\Delta)=\mathbf 1\{\Delta\ge\theta_{\mu^*}((t-1)/n)\}$ belongs to the class, has the same expected cost as Algorithm 2, and satisfies $\mathbb E[\mathrm{ALG}]\le C^*\,\mathrm{OPT}$ on every unit-cost instance.
--
--   The optimality is confined to this information-restricted class.
--
--   Differences from the source:
--   - encoding: lim sup over n of the supremum over instances of size n is at least C* → for every c < C* and every N₀ there are n ≥ N₀ and an instance of size n with E[ALG] > c · OPT; reason: this is the definition of the lim sup bound
--   - generalization: unit-cost prescribed-candidate instances with the rule's fixed tie-breaking → finite unit-cost instances that defeat every nearest-candidate tie order; reason: such an instance is in particular a bad instance for the rule's own tie order
--   - encoding: a rule opening with probability exactly g_n(t, Δ_t) conditional on the complete history → the expected cost on each arrival sequence computed by the recursion that this conditional law determines (rank 1 opens with probability one; an already open nearest candidate costs nothing to open again); reason: the conditional law of every round is pinned down, so the expected cost is the value of this recursion
--   - encoding: Candidate Marginal DistCut at µ* attains the matching upper bound (Theorem B.1) → the indicator rule at µ* is a valid rule, its expected cost equals Algorithm 2's, and E[ALG] ≤ C* · OPT on every unit-cost instance; reason: this is the consequence clause
--   - encoding: µ*, the unique solution in (0,1] of Φ(µ) = 3 + 2µ → the canonical sInf of the solution set in (0,1], with existence, uniqueness and the equation as conclusions; reason: the conclusions exclude the default value of an empty or degenerate solution set without adding a hypothesis
--   - encoding: unit opening costs on a prescribed finite candidate set → the published Geometry with the hypothesis that every fee equals 1; reason: this is the Appendix B setting; the ambient metric remains arbitrary
--   - encoding: a multiset of n demand copies → a map u : Fin n → M (repeated locations allowed); reason: labels distinguish repeated copies for permutation ranks and never enter an online decision
--   - encoding: expectation over the uniformly random arrival order → finite average over all n! permutations of the labeled copies; reason: this is exactly the finite uniform law; no measurability assumption is needed
--   - encoding: every horizon n, including n = 0 (empty multiset, ALG = OPT = 0) → the upper-bound clauses assume 0 < n; reason: at n = 0 the source's bound reads 0 ≤ 0, while the published optimum minimizes over nonempty facility sets; the hypothesis excludes only this degenerate horizon
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Definition B.4 (printed p. 33, PDF p. 35) and Theorem B.5 (printed p. 34, PDF p. 36)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Runs

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

/-- Theorem B.5 (PDF p. 36, printed p. 34). `µ*` is the unique root of `Φ(µ) = 3 + 2µ` in
`(0,1]` and `C* = Φ(µ*) = 3 + 2µ*`. Every Candidate Marginal TimeDist rule has
`limsup_n sup_{|I| = n} E[ALG_G(I)]/OPT(I) ≥ C*` over unit-cost prescribed-candidate instances
(each bad instance is finite and defeats every nearest-candidate tie order). Consequently the
zero-start DistCut rule at `µ*` belongs to the class, coincides with Algorithm 2, and attains
the matching upper bound `C*`. -/
theorem timedist_lower_bound :
    (0 < muStar ∧ muStar ≤ 1 ∧ limitingA muStar = 3 + 2 * muStar ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ 1 → limitingA μ = 3 + 2 * μ → μ = muStar) ∧
    CStar = limitingA muStar ∧ CStar = 3 + 2 * muStar ∧
    (∀ g : ℕ → ℕ → ℝ → ℝ, IsTimeDistRule g → ∀ c : ℝ, c < CStar → ∀ N₀ : ℕ,
      ∃ n : ℕ, N₀ ≤ n ∧ 0 < n ∧
        ∃ (X : Type) (_ : MetricSpace X) (_ : Finite X) (S : Set X), S.Nonempty ∧
          ∃ u : Fin n → X, ∀ G : Geometry X, Set.range G.site = S → (∀ y, G.fee y = 1) →
            c * optimum G u < tdExpected G g u) ∧
    IsTimeDistRule (distCutRule muStar) ∧
    (∀ {M : Type*} [MetricSpace M] (G : Geometry M), (∀ y, G.fee y = 1) →
      ∀ {n : ℕ}, 0 < n → ∀ u : Fin n → M,
        tdExpected G (distCutRule muStar) u = uniformAvg (zeroStartAlg G u muStar) ∧
        uniformAvg (zeroStartAlg G u muStar) ≤ CStar * optimum G u) := by sorry

end RankCutFacility.Shifted.Supplement
