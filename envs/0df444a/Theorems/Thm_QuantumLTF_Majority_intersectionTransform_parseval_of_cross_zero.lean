-- Prove2me | Theorems.Thm_QuantumLTF_Majority_intersectionTransform_parseval_of_cross_zero
-- name    : QuantumLTF.Majority.intersectionTransform_parseval_of_cross_zero
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:27:39.575207+00:00
-- url     : https://prove2.me/theorems/fd0d23f7-de08-436c-be18-d55bd1e645c9
-- title:
--   Scalar Krawtchouk Parseval identity under cross-term cancellation
-- statement:
--   Let
--
--   $$
--   W(a)=\sum_{t=0}^k K_t(a)\bigl(p_t+(-1)^tq_t\bigr).
--   $$
--
--   If the weighted signed cross term vanishes,
--
--   $$
--   \sum_{t=0}^k {k\choose t}(-1)^t p_tq_t=0,
--   $$
--
--   then weighted Krawtchouk Parseval gives
--
--   $$
--   2^{-k}\sum_{a=0}^k{k\choose a}W(a)^2=\sum_{t=0}^k{k\choose t}(p_t^2+q_t^2).
--   $$
--
--   The cancellation hypothesis is exactly what removes the cross term missing from the earlier false scalar statement. In the odd exact-size construction it follows from the complementary supports and endpoint normalization of the two polynomial families.
-- source:
--   Corrected scalar form of the Krawtchouk Parseval calculation used in Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2; weighted Krawtchouk orthogonality plus the source polynomial cross-term cancellation.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

theorem intersectionTransform_parseval_of_cross_zero : ∀ k : ℕ, ∀ p q : Fin (k+1) → ℝ, (∑ t : Fin (k+1), (k.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 → (1/(2:ℝ)^k) * ∑ a : Fin (k+1), (k.choose a : ℝ) * (intersectionTransform k p q a)^2 = ∑ t : Fin (k+1), (k.choose t : ℝ) * (p t^2+q t^2) := by sorry

end QuantumLTF.Majority
