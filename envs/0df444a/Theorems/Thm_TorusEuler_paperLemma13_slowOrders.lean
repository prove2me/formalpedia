-- Prove2me | Theorems.Thm_TorusEuler_paperLemma13_slowOrders
-- name    : TorusEuler.paperLemma13_slowOrders
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T19:38:55.081412+00:00
-- url     : https://prove2.me/theorems/ab00cc1a-18b3-4927-9ec2-deb7b9ea690b
-- title:
--   Lemma 1.3 — slow growth of the derivative orders in the frequency schedule
-- statement:
--   **Lemma 1.3 of the frozen manuscript (cc:uf:tower:lem:slow-orders).** Fix an integer $b\ge1$, a threshold function $B:\mathbb{N}\to\mathbb{R}$, a frequency sequence $\lambda:\mathbb{N}\to\mathbb{R}$ (written `freq`, with $\lambda_i$ = `freq i`), and an order sequence $q:\mathbb{N}\to\mathbb{N}$, and write $K(s)=320b(s+1)$ (`frequencyExponent`). Assume:
--
--   1. $q_1=1$ and $B(1)\le\lambda_0$;
--   2. $\lambda_{i+1}=\lambda_i^{K(q_{i+1})}$ for every $i$;
--   3. for every $i$, $q_{i+2}$ is the greatest element of $\{s: 1\le s\le q_{i+1}+1,\ B(s)\le\lambda_i\}$ (the schedule's max-selection, with the paper's index $j=i+1$);
--   4. $B(s)>0$ and $\log B(s)\ge 4K(s+1)^3$ for every $s\ge1$.
--
--   Then the orders grow by at most one and tend to infinity,
--   $$q_j\le q_{j+1}\le q_j+1\quad(j\ge1),\qquad q_j\to\infty,$$
--   and the logarithmic gains $L_j=4\log\lambda_{j+1}$ obey the uniform bound
--   $$L_{j+1}\le(\log\lambda_{j-1})^2\quad(j\ge1),$$
--   which in the statement's zero-based frequency index reads $4\log\lambda_{i+3}\le(\log\lambda_i)^2$ for all $i$.
--
--   This is the schedule lemma that keeps the fixed-order constant losses of the construction below small powers of the frequencies, however fast $B$ grows; it is proved in Appendix C of the manuscript.
--
--   **Formalization Note** The paper chooses $B$ nondecreasing; the formal statement (the authors' own) does not need monotonicity and assumes only positivity and the floor bound. The order sequence is one-based ($q_1=1$) while frequencies are zero-based ($\lambda_0=N$), exactly as in the schedule (1.14); the docstring records the shift $i=j-1$.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/PaperParameterAndLaunchStatements.lean#L14; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/01b_parameters.tex#L54 (cc:uf:tower:lem:slow-orders), schedule (cc:uf:tower:eq:schedule).

import Mathlib
import Definitions.Def_TorusEuler_Schedule

open Filter Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

/-- `cc:uf:tower:lem:slow-orders`, with `i = j - 1`. The gain `L_(j+1)` is
`4 * log (freq (i+3))` under the schedule in (1.14). -/
theorem paperLemma13_slowOrders (b : ℕ) (B freq : ℕ → ℝ) (q : ℕ → ℕ)
    (hb : 1 ≤ b) (hq : q 1 = 1) (hInitial : B 1 ≤ freq 0)
    (hFrequency : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hMaximum : ∀ i,
      IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2)))
    (hPositive : ∀ s, 1 ≤ s → 0 < B s)
    (hFloor : ∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) :
    (∀ i, q (i + 1) ≤ q (i + 2) ∧ q (i + 2) ≤ q (i + 1) + 1) ∧
      Tendsto q atTop atTop ∧ ∀ i, 4 * Real.log (freq (i + 3)) ≤ (Real.log (freq i)) ^ 2 := by sorry

end TorusEuler
