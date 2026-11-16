-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_Supplement_lemma_6_2
-- name    : PooledTestingAdaptivity.Gap.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:38:31.120203+00:00
-- url     : https://prove2.me/theorems/1999899d-5420-4783-95cb-f1d2095e35d4
-- title:
--   Lemma 6.2 — Conditional split stability
-- statement:
--   Let $J$ be a pooled-testing instance with pool cap $G$ and let $H$ be a history. Let $t$ be a set of at most $G$ individuals that maximizes the conditional gain $g(\cdot\mid H)$ over all sets of at most $G$ individuals, and suppose $g(t\mid H)>0$. Let $U=t\setminus C(H)$ be its uncleared members and $\Sigma=\sum_{i\in U}u_i$. Then
--   $$u_i\ge(1-q_i)\,\Sigma\quad(i\in U),\qquad \sum_{i\in U}(1-q_i)\le1 .$$
--
--   Every member's utility compensates for the risk it adds to the selected pool. The inequalities feed the bound $\sum_{i\in D_j}q_iu_i\le e\,g_j$ in the proof of Theorem 3.8.
--
--   Differences from the source:
--   - generalization: a pool selected by DynamicGreedy with positive gain after a history H it reaches → any maximizer t of g(· | H) over sets of size at most G with g(t | H) > 0, after any history; reason: DynamicGreedy's selection at a reached history satisfies exactly these hypotheses, so the source's statement is the special case
--   - encoding: positive probability of H → implied by g(t | H) > 0; reason: the gain is a ratio with denominator P(H) and is 0 when P(H) = 0
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Lemma 6.2, Eq. (19), printed p. 21, PDF p. 22

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Greedy

namespace PooledTestingAdaptivity.Gap.Supplement

/-- Lemma 6.2 (Conditional split stability), printed p. 21, PDF p. 22: a pool `t` of at most
`G` individuals maximizing `g(· | H)` over all sets of at most `G` individuals, with positive
gain (which forces `P(H) > 0`). `U = t \ C(H)`. -/
theorem lemma_6_2 {n : ℕ} (J : Instance n) (H : History n) (t : Finset (Fin n))
    (ht : t.card ≤ J.cap)
    (hmax : ∀ s : Finset (Fin n), s.card ≤ J.cap → gain J H s ≤ gain J H t)
    (hpos : 0 < gain J H t) :
    (∀ i ∈ t \ histCleared H, (1 - J.q i) * ∑ j ∈ t \ histCleared H, J.u j ≤ J.u i) ∧
      ∑ i ∈ t \ histCleared H, (1 - J.q i) ≤ 1 := by sorry

end PooledTestingAdaptivity.Gap.Supplement
