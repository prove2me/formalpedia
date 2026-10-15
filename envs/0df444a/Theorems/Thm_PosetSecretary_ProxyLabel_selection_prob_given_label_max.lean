-- Prove2me | Theorems.Thm_PosetSecretary_ProxyLabel_selection_prob_given_label_max
-- name    : PosetSecretary.ProxyLabel.selection_prob_given_label_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:30.67448+00:00
-- url     : https://prove2.me/theorems/1f36ce84-da6f-42ff-bf15-5744bb6948c2
-- title:
--   Display (3), proof of Proposition 5.2, p. 17 — given that a_j is maximum in its label class, P(a_j ∈ Alg) ≥ (1/(ω′+1))(1 − 1/(ω′+1))^ω
-- statement:
--   Let $(C, \preceq)$ be a finite poset of width $\omega$ with a consistent scoring $w$, let $k \ge 1$ and $\omega' \in \mathbb N$. Fix an element $a \in C$ and a labelling $\ell : C \to \{1, \dots, k\}$ under which no element of larger score than $a$ has the label of $a$; that is, $a$ is the maximum of its label class. Run ProxyLabel with this labelling, a uniformly random arrival order and a sample of the first $m \sim \mathrm{Bin}(N, \omega'/(\omega'+1))$ arrivals. Then
--
--   $$\mathbb P(a \in \mathrm{Alg} \mid \ell) \ \ge\ \frac{1}{\omega'+1}\Big(1 - \frac{1}{\omega'+1}\Big)^{\omega},$$
--
--   where the probability is over the arrival order and $m$.
--
--   This is the bound (3) on the quantity $A$ of display (2): the conditional probability that a label-class maximum is selected. Together with the label-maximum bound it gives the per-element selection bound of Proposition 5.2.
--
--   **Formalization Note** The paper conditions on the event that $a_j$ is maximum in its labeled group. Since labels are independent of the arrival order and of $m$, the bound is stated here pointwise, for every labelling in that event; averaging over the event recovers $A$ and needs no division by its probability. The width $\omega$ is that of the whole poset, the published `AppliedComb.Posets.width α`.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.2, display (3), p. 17

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

namespace PosetSecretary.ProxyLabel

/-- Display (3), proof of Proposition 5.2, p. 17 (Salem & Gupta, SSRN 3444283): fix a
labelling `ℓ` under which no element scoring above `a` shares the label of `a`. Then the
probability, over a uniformly random arrival order and `m ∼ Bin(N, ω′/(ω′+1))`, that ProxyLabel
selects `a` is at least `(1/(ω′+1)) (1 - 1/(ω′+1))^ω`, where `ω` is the width of the poset. -/
theorem selection_prob_given_label_max {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : IsConsistentScoring w) (k : ℕ) (hk : 1 ≤ k) (ω' : ℕ) (a : α)
    (ℓ : α → Fin k) (hmax : ∀ b, w a < w b → ℓ b ≠ ℓ a) :
    (1 / (ω' + 1 : ℝ)) * (1 - 1 / (ω' + 1 : ℝ)) ^ AppliedComb.Posets.width α ≤
      ∑ pos : α ≃ Fin (Fintype.card α), ∑ m ∈ Finset.range (Fintype.card α + 1),
        (1 / ((Fintype.card α).factorial : ℝ)) *
          binomWeight (Fintype.card α) m (sampleProb ω') *
            (if a ∈ selected pos ℓ m then 1 else 0) := by sorry

end PosetSecretary.ProxyLabel
