-- Prove2me | Theorems.Thm_ReplParity_collect_conditional_law
-- name    : ReplParity.collect_conditional_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:45.526072+00:00
-- url     : https://prove2.me/theorems/00bc04d1-16b0-4fb0-add1-93c263619060
-- title:
--   Proof of Proposition 3.4, pp.17–18 — the collected vectors are i.i.d. from the conditional law
-- statement:
--   Let $Q$ be a distribution on a finite set $\alpha$, let $A\subseteq\alpha$ with $Q(A)>0$, let $K\le R$, and draw $X\sim Q^R$. Say the collection **succeeds** if at least $K$ entries of $X$ lie in $A$, and let the **collected vectors** be the first $K$ such entries, in order. Then for every $w\in A^K$,
--   $$\Pr\big[\text{success and collected}=w\big]=\Pr[\text{success}]\cdot\prod_{i=1}^{K}\frac{Q(w_i)}{Q(A)} .$$
--   That is, conditioned on success, the collected vectors are independent samples from $Q$ conditioned on $A$. In the proof of Proposition 3.4, $\alpha=\mathbb F_2^n$ and $A=\mathbb F_2^n\setminus V_{j-1}$.
--
--   Differences from the source:
--   - generalization: 𝔽ⁿ₂ and the set 𝔽ⁿ₂ \ V_{j−1} → any finite set α and any subset A with Q(A) > 0; reason: specializes to α = 𝔽ⁿ₂, A = 𝔽ⁿ₂ \ V_{j−1}
--   - encoding: conditioned on success, the collected vectors are independent samples from Q conditioned on A → Pr[success ∧ collected = w] = Pr[success] · ∏ Q(wᵢ)/Q(A) for every w ∈ A^K; reason: this identity is the statement that the conditional law of the collected vectors is the product of Q(·)/Q(A)
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Proposition 3.4, pp.17–18 (PDF pp.19–20)

import Mathlib
import Definitions.Def_ReplParity_prIID

namespace ReplParity

/-- **The collected vectors are i.i.d. from the conditional law (proof of Proposition 3.4).** Shen,
Zhong, *Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC
2027 submission (manuscript sha256 40424491…), proof of Proposition 3.4, pp.17–18 (PDF pp.19–20):
"Conditioned on success, the collected vectors are independent samples from Q conditioned on
𝔽ⁿ₂ \ V_{j−1}. To see this, condition on the pattern of which samples lie outside V_{j−1}, and note
that given the pattern the outside samples are independent with this conditional law, while success
depends only on the pattern."

Let `Q` be a distribution on a finite set `α`, `A ⊆ α` with `Q(A) > 0`, `K ≤ R`, and draw
`X ∼ Q^R`. "Success" is that at least `K` entries of `X` lie in `A`; the collected vectors are the
first `K` of them, in index order. For every `w ∈ A^K`,
`Pr[success ∧ collected = w] = Pr[success] · ∏ᵢ Q(wᵢ)/Q(A)`. -/
theorem collect_conditional_law {α : Type*} [Fintype α] [DecidableEq α] (Q : PMF α)
    (A : Finset α) (hA : 0 < ∑ a ∈ A, (Q a).toReal) (K R : ℕ) (hKR : K ≤ R) (w : Fin K → α)
    (hw : ∀ i, w i ∈ A) :
    probIID Q R (fun X => K ≤ ((List.ofFn X).filter (fun a => decide (a ∈ A))).length ∧
        ((List.ofFn X).filter (fun a => decide (a ∈ A))).take K = List.ofFn w) =
      probIID Q R (fun X => K ≤ ((List.ofFn X).filter (fun a => decide (a ∈ A))).length) *
        ∏ i, (Q (w i)).toReal / ∑ a ∈ A, (Q a).toReal := by sorry

end ReplParity
