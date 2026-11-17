-- Prove2me | Theorems.Thm_QuantumLTF_Majority_odd_polynomial_pointwise_witness
-- name    : QuantumLTF.Majority.odd_polynomial_pointwise_witness
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:58:30.387287+00:00
-- url     : https://prove2.me/theorems/e67f9d7b-1fff-4cd9-9d51-c9793cc053f8
-- title:
--   Pointwise odd-support polynomial witness
-- statement:
--   For every odd $r\ge3$, the Section 4.2 polynomial construction provides normalized coefficient families $p_t,q_t$ with complementary interior supports and zero weighted signed cross term. Moreover, for a universal constant $C>0$, every degree satisfies
--
--   $$
--   {r\choose t}(p_t^2+q_t^2)\le C\,\frac{r}{(t+1)(r-t+1)}.
--   $$
--
--   This is the pointwise estimate obtained from the interlacing polynomial construction before summing over degrees.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2 and Lemma 4.3: complementary polynomial construction and pointwise coefficient-energy estimate, with the endpoint and cross-term conditions used by the adversary proof made explicit.

import Mathlib

namespace QuantumLTF.Majority

theorem odd_polynomial_pointwise_witness : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 3 ≤ r → Odd r → ∃ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 ∧ (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 ∧ ∀ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2) ≤ C * (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) := by sorry

end QuantumLTF.Majority
