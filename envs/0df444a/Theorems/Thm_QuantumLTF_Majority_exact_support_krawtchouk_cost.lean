-- Prove2me | Theorems.Thm_QuantumLTF_Majority_exact_support_krawtchouk_cost
-- name    : QuantumLTF.Majority.exact_support_krawtchouk_cost
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:39:36.12786+00:00
-- url     : https://prove2.me/theorems/d0997e8b-9e9c-4fab-a5f5-0fb3652378f3
-- title:
--   Diagonal cost of the exact-support Krawtchouk dual matrix
-- statement:
--   Fix an exact support $A\subseteq[n]$ of size $r$, and form the rank-one dual matrices from the intersection transform $W(|A\cap S|)$. If the signed coefficient cross term vanishes and the coefficient energy is at most $T$, then the diagonal dual objective is at most $T$.
--
--   Indeed, among the $2^n$ Boolean query strings, exactly $2^{n-r}{r\choose a}$ have intersection size $a$ with $A$. Consequently the diagonal sum reduces to the weighted scalar Krawtchouk norm, which corrected Parseval identifies with the coefficient energy.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2, diagonal objective calculation for the rank-one exact-support adversary matrices; corrected scalar Parseval plus Hamming-slice counting.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem exact_support_krawtchouk_cost : ∀ n r : ℕ, r ≤ n → ∀ p q : Fin (r+1) → ℝ, (∑ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 → ∀ T : ℝ, (∑ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2)) ≤ T → let W := intersectionTransform r p q; let X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ := fun S A B => (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S); DualCostAtMost X T := by sorry

end QuantumLTF.Majority
