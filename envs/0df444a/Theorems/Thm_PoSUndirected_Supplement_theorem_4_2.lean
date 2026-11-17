-- Prove2me | Theorems.Thm_PoSUndirected_Supplement_theorem_4_2
-- name    : PoSUndirected.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:32:53.299808+00:00
-- url     : https://prove2.me/theorems/8a4929a9-406c-40d1-82ba-91f2ceb3cc78
-- title:
--   Theorem 4.2 — arbitrary demands at block rank two
-- statement:
--   Consider any finite loopless undirected network-design game with positive real edge costs, arbitrary labelled demand pairs, all simple terminal-to-terminal paths available, maximum physical block rank $b(G)\le2$, and $\mathrm{OPT}>0$. There are an optimum profile $O$ and a weak equilibrium $N$ such that
--   $$
--   C(N)<2C(O)=2\,\mathrm{OPT}.
--   $$
--
--   Moreover, if the whole host is a single theta and some optimum forest profile is unstable, then every global minimum $N$ of Rosenthal's harmonic potential satisfies the same strict inequality relative to every optimum profile.
--
--   Differences from the source:
--   - encoding: cycle rank $|A|-|V(A)|+\operatorname{comp}(V(A),A)$ and $b(G)=\max_B\beta(B)$ → on each connected physical block, the subtraction-free inequality $|E(B)|+1\le|V(B)|+r$; reason: equivalent for connected blocks and avoids truncated natural subtraction
--   - encoding: $\mathrm{PoS}<2$ with $\mathrm{OPT}>0$ → existence of an optimum $O$ and equilibrium $N$ with $C(N)<2C(O)$, plus the positive-optimum hypothesis; reason: the finite game attains both minima and this avoids totalized division
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Theorem 4.2, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_MaxBlockRankLE

open CongestionPoA.AsymSum PriceOfStability.Harmonic

set_option autoImplicit false

namespace PoSUndirected.Supplement

/-- **Theorem 4.2 (arbitrary demands at block rank two).** Tsoufis, preprint sha256
c095d811…, p.7 (PDF p.9).

For every finite positive-cost loopless undirected network-design game with `b(G) ≤ 2` and
positive optimum, some equilibrium costs strictly less than twice optimum.  On a single theta, if
an optimum forest profile is unstable, every global harmonic-potential minimum obeys the same
strict bound.

**Formalization Note.** `MaxBlockRankLE ends 2` is the maximum rank of one physical block, not the
total cycle rank.  The second clause is deliberately local to one theta and retains both the
unstable optimum forest profile and the universal quantifier over potential minima. -/
theorem theorem_4_2 {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (ends : E → Sym2 V) (c : E → ℝ) (s t : ι → V)
    (hloop : IsLoopless ends) (hcost : ∀ e, 0 < c e)
    (hfeas : ∀ i, (pathStrategies ends (s i) (t i)).Nonempty)
    (hrank : MaxBlockRankLE ends 2)
    (hopt : ∃ O : ι → Finset E,
      IsSocialOptimum (ndGame ends c s t) c O ∧ 0 < socialCost c O) :
    (∃ (O N : ι → Finset E),
      IsSocialOptimum (ndGame ends c s t) c O ∧
      IsPureNash (ndGame ends c s t) N ∧
      socialCost c N < 2 * socialCost c O) ∧
    (IsSingleTheta ends →
      (∃ (F : Finset E) (O : ι → Finset E), IsForestProfile ends s t F O ∧
        IsSocialOptimum (ndGame ends c s t) c O ∧
        ¬ IsPureNash (ndGame ends c s t) O) →
      ∀ (N O : ι → Finset E),
        IsGlobalPotentialMinimum (ndGame ends c s t) N →
        IsSocialOptimum (ndGame ends c s t) c O →
        socialCost c N < 2 * socialCost c O) := by sorry

end PoSUndirected.Supplement
