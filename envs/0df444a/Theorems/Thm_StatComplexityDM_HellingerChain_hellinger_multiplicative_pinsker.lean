-- Prove2me | Theorems.Thm_StatComplexityDM_HellingerChain_hellinger_multiplicative_pinsker
-- name    : StatComplexityDM.HellingerChain.hellinger_multiplicative_pinsker
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:22.533189+00:00
-- url     : https://prove2.me/theorems/ddfb4617-a36c-4920-a5cd-e7cc95bb5702
-- title:
--   Lemma A.11, p. 72 — |E_P h − E_Q h| ≤ √(2R(E_P h + E_Q h)·D²_H(P,Q)) and E_P h ≤ 3E_Q h + 4R·D²_H(P,Q)
-- statement:
--   This is the multiplicative Pinsker-type inequality for the Hellinger distance.
--
--   Let $P$ and $Q$ be probability distributions on a finite set $\mathcal Y$, let $R \in \mathbb R$, and let $h : \mathcal Y \to \mathbb R$ satisfy $0 \le h(y) \le R$ for every $y$ with $P(y) > 0$ or $Q(y) > 0$. Write $\mathbb E_P[h] = \sum_y P(y) h(y)$ and similarly for $Q$. Then
--   $$
--   \big|\mathbb E_P[h] - \mathbb E_Q[h]\big| \le \sqrt{2R\,\big(\mathbb E_P[h] + \mathbb E_Q[h]\big)\cdot D^2_{\mathrm H}(P, Q)} \qquad (94)
--   $$
--   and, in particular,
--   $$
--   \mathbb E_P[h] \le 3\,\mathbb E_Q[h] + 4R\, D^2_{\mathrm H}(P, Q). \qquad (95)
--   $$
--
--   Compared with the additive bound $|\mathbb E_P[h] - \mathbb E_Q[h]| \le R\, D_{\mathrm{TV}}(P,Q)$, this gives faster rates when the means are small, at the cost of a multiplicative constant. The proof of Lemma A.13 applies (95) to move an expectation from one sequential law to the other.
--
--   **Formalization Note** Finite alphabets: "almost surely under $P$ and $Q$" becomes "at every point charged by $P$ or by $Q$"; $h$ is unrestricted elsewhere. Both displays are stated as one conjunction.
-- source:
--   arXiv:2112.13487v3, App. A.2, Lemma A.11, (94)–(95), p. 72

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace StatComplexityDM.HellingerChain

open FoundationsRL.GeneralDM

/-- Lemma A.11 (multiplicative Pinsker-type inequality for Hellinger distance,
arXiv:2112.13487v3, p. 72), for probability vectors `P`, `Q` on a finite type: if
`0 ≤ h(x) ≤ R` at every point charged by `P` or `Q` ("almost surely under `P` and `Q`"), then
(94) `|E_P[h] − E_Q[h]| ≤ √(2R(E_P[h] + E_Q[h]) · D²_H(P, Q))` and
(95) `E_P[h] ≤ 3 E_Q[h] + 4R D²_H(P, Q)`. -/
theorem hellinger_multiplicative_pinsker {Y : Type*} [Fintype Y] (P Q : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1)
    (h : Y → ℝ) (R : ℝ) (hh : ∀ y, (0 < P y ∨ 0 < Q y) → 0 ≤ h y ∧ h y ≤ R) :
    |∑ y, P y * h y - ∑ y, Q y * h y| ≤
        Real.sqrt (2 * R * (∑ y, P y * h y + ∑ y, Q y * h y) * hellingerSq P Q) ∧
      ∑ y, P y * h y ≤ 3 * ∑ y, Q y * h y + 4 * R * hellingerSq P Q := by sorry

end StatComplexityDM.HellingerChain
