-- Prove2me | Theorems.Thm_VolDisclosure_Evidence_proposition_4_a
-- name    : VolDisclosure.Evidence.proposition_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:20.125983+00:00
-- url     : https://prove2.me/theorems/fd9da825-4a0e-476c-97e6-804ccfaafa1d
-- title:
--   Proposition 4(a), p. 20, corrected — firm value weakly rises (credit spread weakly falls) in the evidence probability, strictly for v^1(π) < v < v̄
-- statement:
--   Fix parameters $h > l > 0$, $p \in (0,1)$, $r \in (0,1)$, $\lambda \in (0,1]$. For each evidence probability $\pi \in [0,1)$ a firm value $s(\cdot\,;\pi)$ exists (a fixed point of the Bellman operator (T)). Moreover, for $0 \le \pi < \pi' < 1$ and firm values $s = s(\cdot\,;\pi)$, $s' = s(\cdot\,;\pi')$:
--
--   1. for every $v \ge 0$,
--   $$
--   s(v) \le s'(v) \quad\text{and}\quad 1 - \frac{s'(v)}{s^*} \le 1 - \frac{s(v)}{s^*};
--   $$
--   2. for every $v$ with $v^1(\pi) < v < \bar v$,
--   $$
--   s(v) < s'(v) \quad\text{and}\quad 1 - \frac{s'(v)}{s^*} < 1 - \frac{s(v)}{s^*}.
--   $$
--
--   In words: greater availability of evidence weakly raises firm value and weakly lowers the credit spread $1 - s/s^*$ at every promised utility, and strictly so above the first termination threshold $v^1(\pi) = \hat r\bar v/(1+\hat r)$ of the lower evidence probability, below the payout boundary $\bar v = (1+r)p\delta/r$.
--
--   **Why corrected.** The paper states the strict increase for every $v < \bar v$. This fails below $v^1(\pi)$ when $p \le r$: by Proposition 3, at $v^1$ one has $w_h = \bar v$, $w_{dl} = v^1$, $w_{nl} = 0$, so $s(v^1) = (1+r)(r+p)\mu/(r[1+r-(1-p)\pi])$, while $v^1 = r\bar v/(1+r-(1-p)\pi)$. The slope $s(v^1)/v^1 = (1+r)(r+p)\mu/(r^2\bar v)$ of the linear part of $s$ on $[0, v^1]$ therefore does not depend on $\pi$, and $s(v;\pi) = s(v;\pi')$ for $0 \le v \le v^1(\pi)$. The paper's argument ("since $s(\cdot)$ is linear in $v$ for $v < v^1$, the continuity of $s(\cdot)$ implies that $s_\pi(v) > 0$", p. 41) overlooks that $v^1$ moves with $\pi$. The weak inequality holds everywhere, and the strict one on $(v^1(\pi), \bar v)$; at $v \ge \bar v$ both values equal $s^*$.
--
--   **Formalization Note.** The first conjunct (existence of a firm value for every $\pi \in [0,1)$) rules out a vacuous comparison. The lower evidence probability may be $\pi = 0$, the no-evidence benchmark, which the paper compares with $\hat\pi > 0$ in the proof of Proposition 5 (p. 42).
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), p. 20, Proposition 4(a) (corrected; credit spread (7), p. 20); proof p. 41

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

namespace VolDisclosure.Evidence

/-- Proposition 4(a) (p. 20; proof p. 41), corrected: firm value weakly rises and the credit
spread weakly falls in the evidence probability on `R₊`, strictly for `v¹(π) < v < v̄`. -/
theorem proposition_4_a (P : Params) (hP : P.Standing) :
    (∀ π : ℝ, 0 ≤ π → π < 1 → ∃ s, IsValue P π s) ∧
    ∀ (π π' : ℝ) (s s' : ℝ → ℝ), 0 ≤ π → π < π' → π' < 1 →
      IsValue P π s → IsValue P π' s' →
      (∀ v, 0 ≤ v → s v ≤ s' v ∧ creditSpread P s' v ≤ creditSpread P s v) ∧
      (∀ v, P.v1 π < v → v < P.vBar →
        s v < s' v ∧ creditSpread P s' v < creditSpread P s v) := by sorry

end VolDisclosure.Evidence
