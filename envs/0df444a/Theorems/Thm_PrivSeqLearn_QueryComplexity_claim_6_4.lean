-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_claim_6_4
-- name    : PrivSeqLearn.QueryComplexity.claim_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:25.856838+00:00
-- url     : https://prove2.me/theorems/0a232b24-1412-454d-b4d2-7188fafb7847
-- title:
--   Claim 6.4, p. 18 — for the OB strategy every information set I(q) contains the union of guesses G
-- statement:
--   Let $\epsilon > 0$ and $L \ge 2$ be an integer with $2\epsilon < 1/L$, and let $\phi^{\mathrm{OB}}$ be the Opportunistic Bisection strategy with union of guesses $\mathcal G$. For every true value $x \in [0,1)$ and every query sequence $\bar q \in \mathcal Q(x)$ that has positive probability under $\phi^{\mathrm{OB}}$,
--   $$\mathcal G \subseteq \mathcal I(\bar q).$$
--
--   The adversary cannot tell a fictitious bisection (true value in a guess) from a truthful one (true value outside the guesses), so every point of every guess stays consistent with what she observes.
--
--   **Formalization Note** The restriction to $\bar q \in \mathcal Q(x)$ is binding: for a query sequence that no true value produces, the information set is empty. The hypothesis $2\epsilon < 1/L$ is the regime $2\epsilon < \delta \le 1/L$ with $\delta$ eliminated.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18, Claim 6.4

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_OB

namespace PrivSeqLearn.QueryComplexity

/-- Claim 6.4 (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18): for the OB strategy, every information set contains the union of
guesses `G`: for every true value `x ∈ [0, 1)` and every query sequence `q ∈ Q(x)`, `G ⊆ I(q)`.

**Formalization Note** The paper's `I(q)` ranges over observable `q`; for `q` outside every `Q(x)`
the information set is empty, so the quantification over `q ∈ Q(x)` is binding. The hypothesis
`2ϵ < 1/L` is the regime `2ϵ < δ ≤ 1/L` with `δ` eliminated. -/
theorem claim_6_4 (ϵ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hL : 2 ≤ L) (hϵL : 2 * ϵ < 1 / (L : ℝ)) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ q ∈ Qset (obStrategy ϵ L (by omega)) x,
      guessUnion ϵ L ⊆ infoSet (obStrategy ϵ L (by omega)) q := by sorry

end PrivSeqLearn.QueryComplexity
