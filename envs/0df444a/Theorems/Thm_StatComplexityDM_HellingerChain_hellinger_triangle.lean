-- Prove2me | Theorems.Thm_StatComplexityDM_HellingerChain_hellinger_triangle
-- name    : StatComplexityDM.HellingerChain.hellinger_triangle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:22.085496+00:00
-- url     : https://prove2.me/theorems/9191ff94-f4a3-40f7-a9c8-39287116dd55
-- title:
--   Proof of Lemma A.13, p. 73 — the Hellinger distance D_H = √D²_H satisfies the triangle inequality
-- statement:
--   Let $P$, $Q$, $R$ be probability distributions on a finite set $\mathcal Y$, and let $D_{\mathrm H}(P, Q) = \sqrt{D^2_{\mathrm H}(P, Q)}$ be the Hellinger distance, where $D^2_{\mathrm H}(P, Q) = \sum_{y} (\sqrt{P(y)} - \sqrt{Q(y)})^2$. Then
--   $$
--   D_{\mathrm H}(P, R) \le D_{\mathrm H}(P, Q) + D_{\mathrm H}(Q, R).
--   $$
--
--   The proof of Lemma A.13 uses this fact to split $D_{\mathrm H}(\mathbb P, \mathbb Q)$ through an intermediate mixture law $\mathbb P_\lambda$.
--
--   **Formalization Note** Finite alphabets: distributions are probability vectors (nonnegative entries summing to one). The paper states the fact for general probability measures, without a number.
-- source:
--   arXiv:2112.13487v3, App. A.2, proof of Lemma A.13, p. 73 ("Since Hellinger distance satisfies the triangle inequality")

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace StatComplexityDM.HellingerChain

open FoundationsRL.GeneralDM

/-- The triangle inequality for the Hellinger distance `D_H = √(D²_H)` (arXiv:2112.13487v3,
App. A.2, proof of Lemma A.13, p. 73), for probability vectors on a finite type:
`D_H(P, R) ≤ D_H(P, Q) + D_H(Q, R)`. -/
theorem hellinger_triangle {Y : Type*} [Fintype Y] (P Q R : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1)
    (hR : (∀ y, 0 ≤ R y) ∧ ∑ y, R y = 1) :
    Real.sqrt (hellingerSq P R) ≤
      Real.sqrt (hellingerSq P Q) + Real.sqrt (hellingerSq Q R) := by sorry

end StatComplexityDM.HellingerChain
