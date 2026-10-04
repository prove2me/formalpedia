-- Prove2me | Theorems.Thm_StochApproxDyn_LimitSet_limitSet_isInternallyChainTransitive
-- name    : StochApproxDyn.LimitSet.limitSet_isInternallyChainTransitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:19:19.314977+00:00
-- url     : https://prove2.me/theorems/22448547-2e30-42d8-9459-324ea71e991c
-- title:
--   Theorem 5.7 (i) — the limit set of a precompact asymptotic pseudotrajectory is internally chain transitive
-- statement:
--   Let $\Phi$ be a semiflow on an arbitrary metric space $(M,d)$ (not assumed compact, complete or locally compact). Let $X:\mathbb R_+\to M$ be an asymptotic pseudotrajectory of $\Phi$ which is precompact, i.e. its image $X(\mathbb R_+)$ has compact closure in $M$. Then the limit set
--   $$L(X)=\bigcap_{t\ge0}\overline{X([t,\infty))}$$
--   is internally chain transitive: it is nonempty, compact and invariant ($\Phi_t(L(X))=L(X)$ for all $t\ge0$), and for all $a,b\in L(X)$ and all $\delta>0$, $T>0$ there is a $(\delta,T)$-pseudo-orbit of $\Phi$ from $a$ to $b$ all of whose points lie in $L(X)$.
--
--   This is the limit set theorem of Benaïm and Hirsch. Combined with the fact that interpolated stochastic approximation processes are asymptotic pseudotrajectories of the mean ODE, it says that such algorithms converge to internally chain transitive sets of the ODE, and so reduces their asymptotic analysis to the dynamics of the ODE.
--
--   **Formalization Note** A semiflow is Mathlib's `Flow ℝ≥0 M` and $X$ is a function `ℝ≥0 → M`; continuity of $X$ is part of being an asymptotic pseudotrajectory. Nonemptiness of $L(X)$ is part of the conclusion, not a hypothesis.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 24, Theorem 5.7 (i)

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Theorem 5.7 (i) (Benaïm 1999, p. 24): let `Φ` be a semiflow on an arbitrary metric space `M`
and `X : ℝ₊ → M` a precompact asymptotic pseudotrajectory of `Φ`. Then its limit set
`L(X) = ⋂_{t ≥ 0} closure (X([t, ∞)))` is internally chain transitive. -/
theorem limitSet_isInternallyChainTransitive {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (X : ℝ≥0 → M) (hX : IsAsymptoticPseudotrajectory Φ X)
    (hpre : IsCompact (closure (Set.range X))) :
    IsInternallyChainTransitive Φ (limitSet X) := by sorry

end StochApproxDyn.LimitSet
