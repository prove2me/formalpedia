-- Prove2me | Theorems.Thm_StatComplexityDM_TabularPS_multiplicative_pinsker_hellinger
-- name    : StatComplexityDM.TabularPS.multiplicative_pinsker_hellinger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:07.979262+00:00
-- url     : https://prove2.me/theorems/91d6126c-fa2e-450b-b620-f44ee9d344ea
-- title:
--   Lemma A.11 (94)–(95) — multiplicative Pinsker inequality for Hellinger distance
-- statement:
--   Let $P,Q$ be probability laws on a finite set, and let $f$ take values in $[0,R]$ almost surely under both laws, where $R\ge0$. Then
--   $$
--   |\mathbb E_P[f]-\mathbb E_Q[f]|
--     \le\sqrt{2R(\mathbb E_P[f]+\mathbb E_Q[f])D_H^2(P,Q)},
--   \qquad
--   \mathbb E_P[f]\le3\mathbb E_Q[f]+4R D_H^2(P,Q).
--   $$
--   This converts an expectation under one law to an expectation under another with a Hellinger penalty.
--
--   **Formalization Note** The almost-sure bound is imposed only at points in the support of $P$ or $Q$. The alphabet is finite.
-- source:
--   arXiv:2112.13487v3, Lemma A.11, (94)–(95), p. 72

import Mathlib
import Definitions.Def_StatComplexityDM_TabularPS_MDP

namespace StatComplexityDM.TabularPS

/-- Lemma A.11, inequalities (94)–(95), p. 72, on a finite alphabet. -/
theorem multiplicative_pinsker_hellinger {X : Type*} [Fintype X]
    (P Q : X → ℝ) (f : X → ℝ) (R : ℝ)
    (hP : StatComplexityDM.LowerBound.IsDist P) (hQ : StatComplexityDM.LowerBound.IsDist Q) (hR : 0 ≤ R)
    (hf : ∀ x, P x ≠ 0 ∨ Q x ≠ 0 → 0 ≤ f x ∧ f x ≤ R) :
    |(∑ x, P x * f x) - (∑ x, Q x * f x)| ≤
      Real.sqrt (2 * R * ((∑ x, P x * f x) + (∑ x, Q x * f x)) *
        FoundationsRL.GeneralDM.hellingerSq P Q) ∧
    ∑ x, P x * f x ≤
      3 * ∑ x, Q x * f x + 4 * R * FoundationsRL.GeneralDM.hellingerSq P Q := by sorry

end StatComplexityDM.TabularPS
