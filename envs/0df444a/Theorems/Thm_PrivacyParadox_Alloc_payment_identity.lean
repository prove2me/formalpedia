-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_payment_identity
-- name    : PrivacyParadox.Alloc.payment_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:52.487278+00:00
-- url     : https://prove2.me/theorems/9e3bb7c7-03fc-4e4b-834b-33f55bb2e8df
-- title:
--   Proof of Theorem 2, App. C, p. 22 — expected payment equals expected virtual cost plus Σ q_i θ̄*_i (h(ĉ_i) − g(ĉ_i) − w)
-- statement:
--   Let groups $i=1,\dots,I$ satisfy the standing assumptions, with weights $q_i$, and let $A_i$ be allocation rules with $0<A_i\le1$ on $[c_{\min,i},c_{\max,i}]$ that are integrable there. Let $P_i$ be the payment (15)–(16) built from $A_i$, $F_i$ the cost distribution function, $\phi_i$ the virtual cost (20), and $\bar\theta_i=F_i(\hat c_i)$. Then
--   $$
--   \sum_i q_i\int_{c_{\min}}^{\hat c_i}A_i(c)P_i(c)f_i(c)\,dc=\sum_i q_i\int_{c_{\min}}^{\hat c_i}\phi_i(c)A_i(c)f_i(c)\,dc+\sum_i q_i\bar\theta_i\big(h_i(\hat c_i)-g_i(\hat c_i)-w\big).
--   $$
--
--   This identity rewrites the expected payment to a participant, the left side of the budget constraint (7), as an expected virtual cost plus the constant $l$ of (51); it turns the mechanism design problem into the program (36)/(39).
--
--   **Formalization Note** The participation benefit $w=w(\bar\theta^*)$, common to all groups in the paper, is read from each group's data, so the statement also covers group-dependent benefits. Monotonicity of $A_i$ is not needed for the identity; integrability suffices.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, App. C (proof of Theorem 2), pp. 21–22, display before (36)

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

open MeasureTheory

theorem payment_identity {I : ℕ} (G : Fin I → GroupData) (hG : ∀ i, (G i).Standing)
    (q : Fin I → ℝ) (A : Fin I → ℝ → ℝ)
    (hA : ∀ i, ∀ c ∈ (G i).C, 0 < A i c ∧ A i c ≤ 1)
    (hAint : ∀ i, IntervalIntegrable (A i) volume (G i).cmin (G i).cmax) :
    ∑ i, q i * ∫ c in (G i).cmin..(G i).chat, A i c * (G i).pay (A i) c * (G i).f c
      = ∑ i, q i * ∫ c in (G i).cmin..(G i).chat, (G i).phi c * A i c * (G i).f c
        + ∑ i, q i * (G i).F (G i).chat *
            ((G i).h (G i).chat - (G i).g (G i).chat - (G i).wbar) := by sorry

end PrivacyParadox.Alloc
