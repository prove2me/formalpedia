-- Prove2me | Theorems.Thm_StatComplexityDM_HellingerChain_hellingerSq_convex_right
-- name    : StatComplexityDM.HellingerChain.hellingerSq_convex_right
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:20.501621+00:00
-- url     : https://prove2.me/theorems/49cc6a88-3cdd-4b35-bd7d-1186fc1fa7eb
-- title:
--   Proof of Lemma A.13, p. 74 — convexity of D²_H: D²_H(Q,(1−λ)P+λQ′) ≤ (1−λ)D²_H(Q,P) + λD²_H(Q,Q′)
-- statement:
--   Let $Q$, $P$, $Q'$ be probability distributions on a finite set $\mathcal Y$ and let $\lambda \in [0, 1]$. Then the squared Hellinger distance is convex in its second argument:
--   $$
--   D^2_{\mathrm H}\big(Q, (1-\lambda) P + \lambda Q'\big) \le (1-\lambda)\, D^2_{\mathrm H}(Q, P) + \lambda\, D^2_{\mathrm H}(Q, Q').
--   $$
--
--   In the proof of Lemma A.13 this bounds the distance from $Q^{(i)}$ to the mixed kernel $P^{(i)}_\lambda = (1-\lambda)P^{(i)} + \lambda Q^{(i)}$ (with $Q' = Q$) and from $P^{(i)}$ to $P^{(i)}_\lambda$.
--
--   **Formalization Note** Finite alphabets: distributions are probability vectors; the mixture is the pointwise combination of the two vectors. The paper invokes "convexity of squared Hellinger distance" without a number; it is stated here in the argument in which the proof uses it.
-- source:
--   arXiv:2112.13487v3, App. A.2, proof of Lemma A.13, p. 74 ("by convexity of squared Hellinger distance")

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace StatComplexityDM.HellingerChain

open FoundationsRL.GeneralDM

/-- Convexity of the squared Hellinger distance in its second argument (arXiv:2112.13487v3,
App. A.2, proof of Lemma A.13, p. 74), for probability vectors on a finite type and
`λ ∈ [0, 1]`: `D²_H(Q, (1 − λ)P + λQ') ≤ (1 − λ) D²_H(Q, P) + λ D²_H(Q, Q')`. -/
theorem hellingerSq_convex_right {Y : Type*} [Fintype Y] (Q P Q' : Y → ℝ)
    (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1) (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1)
    (hQ' : (∀ y, 0 ≤ Q' y) ∧ ∑ y, Q' y = 1) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    hellingerSq Q ((1 - lam) • P + lam • Q') ≤
      (1 - lam) * hellingerSq Q P + lam * hellingerSq Q Q' := by sorry

end StatComplexityDM.HellingerChain
