-- Prove2me | Theorems.Thm_PrivLearn_Parity_claim_4_3
-- name    : PrivLearn.Parity.claim_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:11.588427+00:00
-- url     : https://prove2.me/theorems/6fc4a792-3483-49b5-8387-9595372713e9
-- title:
--   Claim 4.3 — $\Pr[\mathcal A(z) = h \mid i \in S] \le 2 \Pr[\mathcal A(z) = h \mid i \notin S]$
-- statement:
--   Let $0 < \varepsilon \le 4$, $p = \varepsilon/4$, let $z$ be any database of size $n$, $i \in [n]$, and $c_r$ any parity function. Write $w(T) = p^{|T|}(1-p)^{n-1-|T|}$ for the probability that $\mathcal A$ selects exactly $T$ from $[n] \setminus \{i\}$, and $\pi(S) = \Pr[\mathcal A(z) = c_r \mid S]$, which is $1/|V_S|$ if $r \in V_S$ and $0$ otherwise. Then
--
--   $$
--   \sum_{T \subseteq [n]\setminus\{i\}} w(T)\, \pi(T \cup \{i\}) \;\le\; 2 \sum_{T \subseteq [n]\setminus\{i\}} w(T)\, \pi(T).
--   $$
--
--   The two sums are $\Pr[\mathcal A(z) = c_r \mid i \in S]$ and $\Pr[\mathcal A(z) = c_r \mid i \notin S]$ up to the common factor $1/2$ of step 1, so this is the paper's statement that their ratio is at most $2$. It is the key estimate in the privacy proof of $\mathcal A$ (Lemma 4.2).
--
--   **Formalization Note** The paper writes the ratio. The product form avoids division by zero; it agrees with the ratio whenever the denominator is positive, and when the denominator vanishes the paper shows the numerator vanishes too, which the product form also asserts.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 15, Claim 4.3 (proof p. 16)

import Mathlib
import Definitions.Def_PrivLearn_Parity_Learner

namespace PrivLearn.Parity

/-- Claim 4.3, p. 15, in product form. For every database `z ∈ Dⁿ`, every index `i` and every
hypothesis `c_r`, with `p = ε/4`,
`∑_{T ⊆ [n]∖{i}} p^{|T|}(1−p)^{n−1−|T|} Pr[A(z) = c_r | S = T ∪ {i}]
  ≤ 2 ∑_{T ⊆ [n]∖{i}} p^{|T|}(1−p)^{n−1−|T|} Pr[A(z) = c_r | S = T]`,
i.e. `Pr[A(z) = c_r | i ∈ S] ≤ 2 Pr[A(z) = c_r | i ∉ S]` (the common factor `1/2` of step 1
cancels). -/
theorem claim_4_3 {d n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 4) (z : Fin n → Example d)
    (i : Fin n) (r : Fin d → ZMod 2) :
    ∑ T ∈ (Finset.univ.erase i).powerset,
        (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) * outProb z (insert i T) r ≤
      2 * ∑ T ∈ (Finset.univ.erase i).powerset,
        (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) * outProb z T r := by sorry

end PrivLearn.Parity
