-- Prove2me | Theorems.Thm_TalluriMNLFull_Policy_proposition_6_full
-- name    : TalluriMNLFull.Policy.proposition_6_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:00:22.965736+00:00
-- url     : https://prove2.me/theorems/b70b6254-47d5-4eb8-80e5-98cd9074b625
-- title:
--   Proposition 6 — nondominated assortments and optimal nested policy (corrected: fare ties and empty set)
-- statement:
--   Fix any finite number $n$ of products, weights $w_j>0$, weakly decreasing fares $r_1\ge\cdots\ge r_n\ge0$, a constant arrival probability $a\in[0,1]$, and finite horizon $H$ and capacity $C$. All subsets, including $\emptyset$, are feasible. The MNL law is $P_j(S)=w_j/(1+\sum_{i\in S}w_i)$ on $S$ and zero off $S$. Nondominance uses both strict branches of Definition 1, with mixtures over all offer sets.
--
--   The corrected Proposition 6 has both conclusions:
--   $$
--   S\text{ nondominated}\quad\Longrightarrow\quad
--   \forall i\notin S\;\forall j\in S,\ r_i\le r_j;
--   $$
--   and there is one function $k_t(x)\in\{0,\ldots,n\}$ defining the actual policy $\pi_t(x)=A_{k_t(x)}$, with $A_k=\{1,\ldots,k\}$, such that
--   $$
--   k_t(0)=0,\qquad x\le y\le C\Longrightarrow k_t(x)\le k_t(y),\qquad
--   J^\pi_t(x)=V_t(x)\quad(0\le t\le H,\ 0\le x\le C).
--   $$
--   At each positive state in that rectangle the same policy chooses an all-subsets Bellman maximizer. Every admissible randomized Markov rule $\mu$ satisfies $J^\mu_t(x)\le J^\pi_t(x)$ there. Both achieved revenues are independently evaluated from the source sale/no-sale probabilities; $V$ is the published full Bellman recursion, not a prefix-restricted optimum.
--
--   The frontier clause says a nondominated set is a prefix after reordering within equal-fare blocks; the reordering can depend on the set. It does not assert that every prefix is nondominated. The dynamic policy uses the original fixed fare order, permits equal and zero fares, and is one selector across all capacities, rather than a collection of unrelated statewise existence claims.
--
--   **Formalization Note** The theorem has no hypothesis asserting marginal monotonicity, prefix optimality, or an optimal selector. Its optimality conclusion includes the $t=0$ and $x=0$ revenue boundaries, and separately states the zero-capacity offer convention. The static Definition 4 property alone is not the conclusion.
--
--   Differences from the source:
--   - correction: Proposition 6 lists only the fixed-order complete sets A_k, k=1,...,n, as nondominated → every nondominated set has no strict fare inversion, including the empty set and arbitrary selections inside fare ties; reason: with n=2, w=(1,1), r=(1,1), a=1/2, H=2, C=1, every assortment and mixture satisfies R=Q; hence both strict dominance branches are impossible for the incomplete singleton {2} and for the empty set
--   - encoding: products 1,...,n, weights exp(u_j), outside weight exp(0)=1, arrival lambda, and backwards time → Fin n represents product i+1; arbitrary strictly positive real weights, outside weight 1, arrival a, and periods remaining t; reason: every positive weight is exp(log w), and these are exactly the source probability law and time convention; no weight bound or strict fare ordering is added
--   - encoding: an optimal nested allocation policy in Definition 3 and Proposition 6, with randomization providing no improvement on p. 8 → one index function defines a fixed-order prefix policy, is nondecreasing in capacity, earns the independently defined full Bellman value, selects Bellman maximizers, and dominates all admissible randomized Markov rules on the finite rectangle; reason: explicit policy evaluation and finite probability mixtures spell out the source control problem; zero-capacity offers and all zero-horizon revenues are empty or zero, and no history-dependent comparison is claimed
--   - generalization: a finite list of n fare products → n may also be zero; reason: the empty-product instance has only the empty offer, zero revenue, and index 0, so the statement specializes to every nonempty source instance
-- source:
--   Talluri and van Ryzin, Revenue Management Under a General Discrete Choice Model of Consumer Behavior, UPF Economics Working Paper 533, October 21, 2001, Proposition 6, proof pp. 24–25; standing model p. 5; equations (1)–(3) p. 7; Definition 1 p. 8; Definition 3 p. 15, printed p. 23 (PDF p. 23), https://econ-papers.upf.edu/papers/533.pdf; PDF SHA-256 053050fd8f6c12672e0e41e7782705b4f3a78b906f24bb52c7697a6d8c453c2c.

import Mathlib
import Definitions.Def_TalluriMNLFull_Policy_Frontier
import Definitions.Def_TalluriMNLFull_Policy_Control

namespace TalluriMNLFull.Policy

/-- Proposition 6 (UPF WP 533, 2001-10-21, p. 23; proof pp. 24–25), corrected
at fare ties and the empty set. For n=2, w=(1,1), r=(1,1), all mixtures satisfy
R=Q, so {2} and the empty set are nondominated. The fixed-order-prefix assertion
is therefore replaced by no strict fare inversion. The dynamic policy clause
is retained on the full weak-fare-order domain, with explicit value attainment. -/
theorem proposition_6_full {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (horder : Antitone r)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (H C : ℕ) :
    (∀ S : Finset (Fin n), ChoiceRM.Policy.IsNondominated (ChoiceRM.MNL.mnl w) r S →
      NoStrictFareInversion r S) ∧
    ∃ k : ℕ → ℕ → Fin (n + 1),
      (∀ t, (k t 0).val = 0) ∧
      IsAdmissible (prefixPolicy k) ∧
      IsFareOrderNested H C (prefixPolicy k) k ∧
      (∀ t x, t ≤ H → x ≤ C →
        policyRevenue a (ChoiceRM.MNL.mnl w) r (prefixPolicy k) t x =
          ChoiceRM.Policy.V a (ChoiceRM.MNL.mnl w) r t x) ∧
      (∀ t x, 1 ≤ t → t ≤ H → 1 ≤ x → x ≤ C →
        ChoiceRM.Policy.IsOptimalOffer a (ChoiceRM.MNL.mnl w) r t x (prefixPolicy k t x)) ∧
      (∀ μ : RandomizedPolicy n, IsRandomizedPolicy μ →
        ∀ t x, t ≤ H → x ≤ C →
          randomizedRevenue a (ChoiceRM.MNL.mnl w) r μ t x ≤
            policyRevenue a (ChoiceRM.MNL.mnl w) r (prefixPolicy k) t x) := by sorry

end TalluriMNLFull.Policy
