-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_dominance_interval
-- name    : RealPinwheel.FiveSixths.dominance_interval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:36:05.211682+00:00
-- url     : https://prove2.me/theorems/bcaad7bd-034f-4d6d-baa3-3b3bf6367f95
-- title:
--   Section 3, equation (2) and endpoint rule — exact dominance interval
-- statement:
--   Let $w$ be an $n$-word of length $L$, let $i$ be a task, let $m_i>0$ be its number of occurrences, and let $G_i(k)$ be its maximum cyclic distance to the $k$-th following occurrence. The operational interval $I_i(w)$ requires every window condition of the repeated schedule at period $1/d$. Put
--
--   $$u_i=\min\left(\{m_i/L\}\cup\left\{\frac{k}{G_i(k)-1}:1\le k\le m_i,\ G_i(k)>1\right\}\right).$$
--
--   Then $u_i>0$. The interval is $(0,u_i)$ if any retained gap bound attains this minimum, and is $(0,u_i]$ otherwise. Equivalently, for every positive real density $d$,
--
--   $$d\in I_i(w)\ \Longleftrightarrow\ dL\le m_i\ \land\ \bigl(\forall k\in\{1,\ldots,m_i\},\ G_i(k)>1\Rightarrow d(G_i(k)-1)<k\bigr).$$
--
--   This is a characterization of the independently defined interval, not merely a formula assigning a number to a variable. The strict gap inequalities determine whether a face of the dominance box is included.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
--   - encoding: the interval is open or closed at its upper endpoint → a set of positive d with d<u or d=u and no minimizing gap term; reason: this set is exactly the stated open or closed interval; the finite-test equivalence is the characterization proved immediately below equation (2)
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Section 3, equation (2) and endpoint rule, printed p. 8 (PDF p. 9)

import Definitions.Def_RealPinwheel_FiveSixths_Word

namespace RealPinwheel.FiveSixths

/-- Section 3, equation (2) and endpoint rule, printed p. 8 (PDF p. 9).
The endpoint is the finite minimum defined in endpointBounds; the interval itself
was independently defined by all window obligations. -/
theorem dominance_interval {n : ℕ} (w : Word n) (i : Fin n) :
    0 < endpoint w i ∧
    admissibleDensities w i =
      {d | 0 < d ∧ (d < endpoint w i ∨ d = endpoint w i ∧ closedEndpoint w i)} ∧
    ∀ d : ℝ, 0 < d →
      (d ∈ admissibleDensities w i ↔
        d * (w.length : ℝ) ≤ (occurrences w i : ℝ) ∧
        ∀ k ∈ Finset.Icc 1 (occurrences w i), 1 < cyclicGap w i k →
          d * ((cyclicGap w i k : ℝ) - 1) < (k : ℝ)) := by sorry

end RealPinwheel.FiveSixths
