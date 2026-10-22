-- Prove2me | Theorems.Thm_RiskFunctionals_StochDominance_quantile_le_iff
-- name    : RiskFunctionals.StochDominance.quantile_le_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:42.972678+00:00
-- url     : https://prove2.me/theorems/011d8c8a-53ee-46be-b6d6-023457a7567c
-- title:
--   Proposition 1.1(iii) — $G^{-1}(p)\le u$ if and only if $p\le G(u)$
-- statement:
--   Let $G$ be the distribution function and $G^{-1}(p) = \inf\{u : G(u)\ge p\}$ the quantile function of a probability law on $\mathbb R$. Let $0 < p \le 1$ be such that $G^{-1}(p)$ is finite, i.e. $G(v) \ge p$ for some $v$ (this holds for every $p<1$). Then for every $u \in \mathbb R$,
--   $$G^{-1}(p) \le u \quad\Longleftrightarrow\quad p \le G(u). \tag{1.6}$$
--
--   This Galois-connection property of the left-continuous quantile function is what makes the quantile transform work and is used throughout the comparison of distribution and quantile functions.
--
--   **Formalization Note** The book states (1.6) without a range for $p$; the quantile function (1.3) is defined for $0<p\le1$, and the statement is formalized on that domain. At $p = 1$ the book's $G^{-1}(1)$ may be $+\infty$, for which Lean has no real value (the `sInf` of the empty set is $0$); the hypothesis that $\{v : G(v)\ge p\}$ is nonempty excludes exactly that case, and it is automatic for $p<1$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 7, Proposition 1.1(iii), Eq. (1.6)

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

namespace RiskFunctionals.StochDominance

open MeasureTheory

/-- Proposition 1.1(iii), (1.6) (Pflug & Römisch, p. 7): `G⁻¹(p) ≤ u` if and only if
`p ≤ G(u)`, for `p` in the domain `0 < p ≤ 1` of the quantile function (1.3) at which
`G⁻¹(p)` is finite (automatic for `p < 1`). -/
theorem quantile_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (p u : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hfin : ∃ v : ℝ, p ≤ distributionFunction μ v) :
    quantileFunction μ p ≤ u ↔ p ≤ distributionFunction μ u := by sorry

end RiskFunctionals.StochDominance
