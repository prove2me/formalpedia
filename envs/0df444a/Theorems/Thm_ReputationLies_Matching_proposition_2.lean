-- Prove2me | Theorems.Thm_ReputationLies_Matching_proposition_2
-- name    : ReputationLies.Matching.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:04.758805+00:00
-- url     : https://prove2.me/theorems/6883476c-74e5-4aec-b1fe-6c6844c7aa93
-- title:
--   Proposition 2 (first sentence), p. 15 (PDF 17) — in equilibrium the adviser's probability of lying decreases in his reputation
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   Let $0 < r \le r'$, and take any equilibrium at reputation $r$ and any equilibrium at reputation $r'$. Write $\Pr_r(\text{lie})$ for the probability that an adviser with a low-skilled candidate recommends him. Then
--   $$\Pr_{r'}(\text{lie}) \le \Pr_r(\text{lie}),$$
--   and the inequality is strict whenever $r < r'$ and $L(r) < \bar B$.
--
--   The higher an adviser's reputation, the more he has to lose from an unsuccessful hire (Assumption (A1)), so he lies less. This is the first sentence of Proposition 2; the second sentence (the firm's ex-ante payoff increases in $r$) is not part of this statement.
--
--   **Formalization Note.** "Decreases" is read as weakly decreasing on $(0,\infty)$ and strictly decreasing from every $r$ with $L(r) < \bar B$. On $\{r : L(r) \ge \bar B\}$ the adviser never lies (Proposition 1), so the lying probability is constant there and a strict decrease on all of $(0, \infty)$ would be false.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), p. 15 (PDF 17), Proposition 2, first sentence; proof p. 39 (PDF 41)

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- Proposition 2 (first sentence), p. 15: in equilibrium the probability that an adviser with a
low-skilled candidate lies is weakly decreasing in the reputation `r`, and strictly decreasing
from every `r` with `L(r) < B̄`. -/
theorem proposition_2 (P : Primitives) (hP : P.Standing) :
    ∀ (r r' : ℝ) (σ σ' : Profile), 0 < r → r ≤ r' →
      IsEquilibrium P σ r → IsEquilibrium P σ' r' →
        lieProb P σ' ≤ lieProb P σ ∧
        (r < r' → P.L r < P.Bbar → lieProb P σ' < lieProb P σ) := by sorry

end ReputationLies.Matching
