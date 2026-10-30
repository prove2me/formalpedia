-- Prove2me | Theorems.Thm_PandoraOrder_Tree_claim_3
-- name    : PandoraOrder.Tree.claim_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:01:56.730931+00:00
-- url     : https://prove2.me/theorems/94382194-a6d3-4004-bd22-e79dbadba0a8
-- title:
--   Claim 3 — extension monotonicity, prefix locality and stopping-time invariance
-- statement:
--   Let $L$ be a line of distinct boxes, $i$ a valid position, and $z_i$ the least nonnegative root for its suffix. All three printed properties are asserted:
--
--   1. Appending any distinct additional boxes at the end cannot decrease $z_i$.
--   2. Let $d(i)$ be the last position before the first strictly smaller following threshold, or the last box if there is none. Then $z_i$ equals the threshold computed on $[b_i,\ldots,b_{d(i)}]$. If $d(i)=i$, it equals the classical real reservation value $\zeta_i$.
--   3. If every later suffix threshold is strictly larger than $z_i$, then for every $0\le y\le z_i$ the auxiliary optimal stopping times at incumbents $z_i$ and $y$ agree almost surely under the independent product law.
--
--   Equal thresholds remain inside the prefix, both endpoints of the incumbent interval are included, and no out-of-range threshold is read. Zero-mass atom combinations are irrelevant to almost-sure equality. The auxiliary rule is the deterministic optimal-continuation Bellman rule; it uses the p. 8 positive-equality convention, not Algorithm 1's strict stopping convention.
--
--   The printed singleton identity is retained even when it is false: at $X=0,c=1$, $z_i=0$ while $\zeta_i=-1$. The classical value has not been clamped or repaired.
--
--   Differences from the source:
--   - encoding: independent finite-support nonnegative box rewards and nonnegative costs → Fin-indexed boxes and atom tables with real masses, allowing repeated atoms and zero masses, and real nonnegative costs; reason: finite sums give the same product experiment; no rationality, common grid, positivity of costs, or normalization is imposed
--   - reading: page 7 conditions on reaching an incumbent, while Appendix C evaluates every nonnegative incumbent → restart the remaining suffix with its independent future laws and a specified incumbent; reason: this preserves the off-support incumbents required by equation (9) and exact threshold computation
--   - encoding: suffix i through n and endpoint d(i) immediately before a strictly smaller following threshold → zero-based drop i and a prefix length through that endpoint, including the end-of-line case; reason: all indices are bounded, equal thresholds stay in the prefix, and neither endpoint of the incumbent interval is deleted
--   - reading: Definition 2 introduces the classical least real root for positive cost, while Claim 3 also ranges over the zero-cost model → use the same least-real-root equation at zero cost as well, without truncating negative roots at positive cost; reason: finite support gives a least root also at zero cost; the printed singleton identity and its positive-cost counterexample are retained
--   - reading: the auxiliary optimal stopping time continues at an equality threshold on page 8 → the deterministic auxiliary Bellman rule continues whenever continuing is optimal, including positive equality thresholds; reason: at zero a continuing optimal action need not exist; this is the BRIEF reading and does not repair Claim 2 or Claim 3
--   - encoding: equality of random stopping times on the given independent reward experiment → equality of the numbers of future openings on every positive-weight product atom; reason: finite support makes this exactly almost-sure equality; adding the common suffix starting index recovers the paper's last-opened-box stopping time, and zero-mass atoms impose no extra event
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, Claim 3, p. 8 (PDF p. 8); https://arxiv.org/abs/2002.06968v2

import Definitions.Def_PandoraOrder_Tree_Contracts

namespace PandoraOrder.Tree

theorem claim_3 {n : ℕ} (I : Instance n) (L : List (Fin n)) (hL : L.Nodup)
    (i : ℕ) (hi : i < L.length) :
    (∀ E : List (Fin n), (L ++ E).Nodup →
      threshold I (L.drop i) ≤ threshold I ((L ++ E).drop i)) ∧
    (threshold I (L.drop i) =
      threshold I ((L.drop i).take (prefixLength I (L.drop i)))) ∧
    (prefixLength I (L.drop i) = 1 →
      threshold I (L.drop i) = classicalReservation I L[i]) ∧
    ((∀ j : ℕ, i < j → j < L.length →
      threshold I (L.drop i) < threshold I (L.drop j)) →
      ∀ y : ℝ, 0 ≤ y → y ≤ threshold I (L.drop i) →
      ∀ ω : (b : Fin n) → Fin (I.size b), outcomeWeight I ω ≠ 0 →
        auxiliaryStop I (L.drop i) (threshold I (L.drop i)) (fun b => I.reward b (ω b)) =
        auxiliaryStop I (L.drop i) y (fun b => I.reward b (ω b))) := by sorry

end PandoraOrder.Tree
