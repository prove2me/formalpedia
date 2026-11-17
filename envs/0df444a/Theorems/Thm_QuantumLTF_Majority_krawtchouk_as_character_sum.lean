-- Prove2me | Theorems.Thm_QuantumLTF_Majority_krawtchouk_as_character_sum
-- name    : QuantumLTF.Majority.krawtchouk_as_character_sum
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-16T20:25:45.805326+00:00
-- url     : https://prove2.me/theorems/97ccc0ea-5e09-4c52-8a09-e7b36a58d636
-- title:
--   Krawtchouk polynomials as fixed-weight character sums
-- statement:
--   Fix a canonical subset $A_a=\{0,\ldots,a-1\}\subseteq\{0,\ldots,k-1\}$. The binary Krawtchouk polynomial is the sum of Walsh characters over all subsets of weight $t$:
--
--   $$
--   K_t(a)=\sum_{\substack{T\subseteq[k]\\|T|=t}}(-1)^{|T\cap A_a|}.
--   $$
--
--   Grouping the subsets $T$ by $j=|T\cap A_a|$ recovers the defining binomial sum. This representation connects the polynomial definition used in Section 4 to Fourier analysis on the Boolean cube.
-- source:
--   Standard character-sum representation of binary Krawtchouk polynomials; Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Sections 4.2–4.3, Krawtchouk transform used in the adversary construction.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

theorem krawtchouk_as_character_sum : ∀ k : ℕ, ∀ t a : Fin (k+1), (krawtchouk k t a : ℤ) = ∑ T ∈ (Finset.univ : Finset (Fin k)).powersetCard (t : ℕ), (-1 : ℤ) ^ ((T ∩ (Finset.univ.filter fun i : Fin k => (i : ℕ) < (a : ℕ))).card) := by sorry

end QuantumLTF.Majority
