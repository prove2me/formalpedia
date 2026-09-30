-- Prove2me | Theorems.Thm_RevenueManagement_choice_optimal_policy
-- name    : RevenueManagement.choice_optimal_policy
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:33:56.730968+00:00
-- url     : https://prove2.me/theorems/6b59c23a-88c3-4ffb-b471-a009dc12e552
-- title:
--   Theorem 2.3: an efficient set maximizing (2.27) is optimal for the choice-based model, and the largest optimal set in the efficient order is increasing in the remaining capacity x and in time t
-- statement:
--   In the choice-based model with a choice model, arrival probabilities $\lambda_t \in [0, 1]$
--   that are positive in every period $1 \le t \le T$, and nonnegative prices:
--
--   (a) in every period $t$ with $x \ge 1$ units remaining some efficient set $S$ maximizes
--   $\lambda_t (R(S) - Q(S)\Delta V_{t+1}(x))$ over all offer sets, and
--   $V_t(x) = \lambda_t (R(S) - Q(S)\Delta V_{t+1}(x)) + V_{t+1}(x)$;
--
--   (b) for fixed $t$ and $1 \le x \le x'$, every efficient optimal set at $x$ is matched by an
--   efficient optimal set at $x'$ with at least as large a purchase probability;
--
--   (c) for fixed $x \ge 1$ and $1 \le t \le t' \le T$, every efficient optimal set in period
--   $t$ is matched by an efficient optimal set in period $t'$ with at least as large a purchase
--   probability.
--
--   Since the efficient sets are indexed in increasing order of $Q$, (b) and (c) say that the
--   largest optimal index $k^*$ is nondecreasing in $x$ and in $t$.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 69, Theorem 2.3 ('An optimal policy for (2.24) is to select a set k* from among the m efficient, ordered sets {Sk : k = 1, ..., m} that maximizes (2.27). Moreover, for a fixed t, the largest optimal index k* is increasing in the remaining capacity x, and for any fixed x, k* is increasing in time t')

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem choice_optimal_policy {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
    (hpos : ∀ t, 1 ≤ t → t ≤ T → 0 < lam t) (hp : ∀ j, 0 ≤ p j) :
    (∀ t x, 1 ≤ t → t ≤ T → 1 ≤ x → ∃ S, IsEfficient P p S ∧ IsChoiceOptimal lam P p T t x S ∧
      choiceValue lam P p T t x = choiceObj lam P p T t x S + choiceValue lam P p T (t + 1) x) ∧
    (∀ t x x', 1 ≤ t → t ≤ T → 1 ≤ x → x ≤ x' → ∀ S, IsEfficient P p S →
      IsChoiceOptimal lam P p T t x S → ∃ S', IsEfficient P p S' ∧
        IsChoiceOptimal lam P p T t x' S' ∧ purchaseProb P S ≤ purchaseProb P S') ∧
    (∀ t t' x, 1 ≤ t → t ≤ t' → t' ≤ T → 1 ≤ x → ∀ S, IsEfficient P p S →
      IsChoiceOptimal lam P p T t x S → ∃ S', IsEfficient P p S' ∧
        IsChoiceOptimal lam P p T t' x S' ∧ purchaseProb P S ≤ purchaseProb P S') := by sorry

end RevenueManagement
