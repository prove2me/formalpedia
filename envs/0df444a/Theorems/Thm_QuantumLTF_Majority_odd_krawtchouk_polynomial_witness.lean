-- Prove2me | Theorems.Thm_QuantumLTF_Majority_odd_krawtchouk_polynomial_witness
-- name    : QuantumLTF.Majority.odd_krawtchouk_polynomial_witness
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:36:18.554661+00:00
-- url     : https://prove2.me/theorems/56448012-3939-4454-afc7-aa184a5f550b
-- title:
--   Odd-support Krawtchouk polynomial witnesses of logarithmic energy
-- statement:
--   There is a universal constant $C>0$ such that every odd $r\ge3$ admits two real coefficient families $p_t,q_t$ with the endpoint normalization and complementary interior support required by the Section 4.2 adversary construction, whose weighted signed cross term vanishes, and whose total binomial energy satisfies
--
--   $$
--   \sum_{t=0}^r {r\choose t}(p_t^2+q_t^2)\le C\log r.
--   $$
--
--   These are the polynomial witnesses constructed from the interlacing zero sets in the paper. The explicit cross-term condition is included because it is required by the corrected scalar Parseval identity.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2, especially the polynomial construction and estimates summarized in Lemma 4.3 and used in Lemma 4.5.

import Mathlib

namespace QuantumLTF.Majority

theorem odd_krawtchouk_polynomial_witness : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 3 ≤ r → Odd r → ∃ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 ∧ (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2)) ≤ C * Real.log r := by sorry

end QuantumLTF.Majority
