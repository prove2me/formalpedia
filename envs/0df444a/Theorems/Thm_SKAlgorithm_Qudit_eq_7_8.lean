-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_eq_7_8
-- name    : SKAlgorithm.Qudit.eq_7_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:58.389381+00:00
-- url     : https://prove2.me/theorems/2c30212d-b899-4ecb-9c44-aa88d98675c7
-- title:
--   Eqs. (7)–(8), p. 7 — the depth needed for accuracy ε, and 5ⁿ = O(ln^{ln 5/ln(3/2)}(1/ε))
-- statement:
--   Let $c > 0$ and $\epsilon_0 > 0$ with $\epsilon_0 c^2 < 1$. There is a constant $K > 0$ such that for every $\epsilon > 0$ there is a depth $n \in \mathbb N$ with
--   $$\frac{1}{c^2}\left(\epsilon_0 c^2\right)^{(3/2)^n} < \epsilon \qquad \text{and} \qquad 5^n \le K \, \ln\!\left(2 + \frac{1}{\epsilon}\right)^{\ln 5 / \ln(3/2)} .$$
--
--   By Eq. (4) the first inequality says $\epsilon_n < \epsilon$; since the sequence returned at depth $n$ has length at most $5^n l_0$, the second gives the length bound $l_\epsilon = O(\ln^{\ln 5/\ln(3/2)}(1/\epsilon))$ of Eq. (8), with exponent $\ln 5/\ln(3/2) \approx 3.97$.
--
--   **Formalization Note.** The depth is existential; the paper's explicit choice, Eq. (7), $n = \lceil \ln[\ln(1/\epsilon c^2)/\ln(1/\epsilon_0 c^2)] / \ln(3/2) \rceil$, gives $\epsilon_n \le \epsilon$, and the strict inequality needed later may require one more level, which $K$ absorbs. $K$ is chosen before $\epsilon$. $\ln(1/\epsilon)$ is replaced by $\ln(2 + 1/\epsilon)$ so that the bound is meaningful for every $\epsilon > 0$, including $\epsilon \ge 1$; as $\epsilon \to 0$ the two are asymptotically equal, so the $O$-class is the same.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 7, Eqs. (7)–(8)

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem eq_7_8 (c ε₀ : ℝ) (hc : 0 < c) (hε₀ : 0 < ε₀) (hlt : ε₀ * c ^ 2 < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      1 / c ^ 2 * (ε₀ * c ^ 2) ^ (((3 : ℝ) / 2) ^ n) < ε ∧
      (5 : ℝ) ^ n ≤ K * Real.log (2 + 1 / ε) ^ (Real.log 5 / Real.log (3 / 2)) := by sorry

end SKAlgorithm.Qudit
