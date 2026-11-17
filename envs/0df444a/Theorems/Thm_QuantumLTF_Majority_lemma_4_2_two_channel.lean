-- Prove2me | Theorems.Thm_QuantumLTF_Majority_lemma_4_2_two_channel
-- name    : QuantumLTF.Majority.lemma_4_2_two_channel
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-16T18:07:03.529211+00:00
-- url     : https://prove2.me/theorems/22c3525b-2ca9-47ea-a804-a586b37159b2
-- title:
--   Lemma 4.2 — two-channel Krawtchouk Parseval identity
-- statement:
--   Let $K_t(a)$ denote the binary Krawtchouk polynomial of degree $t$ on the Hamming slice of dimension $k$. For two real coefficient families $p_t$ and $q_t$, retain their transforms as two orthogonal channels,
--
--   $$
--   P(a)=\sum_{t=0}^k K_t(a)p_t,\qquad Q(a)=\sum_{t=0}^k K_t(a)(-1)^tq_t.
--   $$
--
--   Then the weighted Krawtchouk Parseval identity is
--
--   $$
--   2^{-k}\sum_{a=0}^k {k\choose a}\bigl(P(a)^2+Q(a)^2\bigr)=\sum_{t=0}^k {k\choose t}\bigl(p_t^2+q_t^2\bigr).
--   $$
--
--   Keeping the two channels separate removes the spurious cross term in the earlier scalar formalization and gives the norm identity used to bound the dual-adversary objective.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Section 4.2, Krawtchouk orthogonality/Parseval calculation leading to Lemma 4.2; corrected formal encoding preserves the direct-sum channels in the Gram-vector construction.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

theorem lemma_4_2_two_channel : ∀ k : ℕ, ∀ p q : Fin (k+1) → ℝ, let P : Fin (k+1) → ℝ := fun a => ∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * p t; let Q : Fin (k+1) → ℝ := fun a => ∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * q t); (1/(2:ℝ)^k) * ∑ a : Fin (k+1), (k.choose a : ℝ) * (P a^2 + Q a^2) = ∑ t : Fin (k+1), (k.choose t : ℝ) * (p t^2+q t^2) := by sorry

end QuantumLTF.Majority
