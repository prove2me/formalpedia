-- Prove2me | Theorems.Thm_QuantumLTF_Majority_odd_exact_family_to_all_sizes
-- name    : QuantumLTF.Majority.odd_exact_family_to_all_sizes
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T00:53:48.762784+00:00
-- url     : https://prove2.me/theorems/087e3fe2-8249-4d91-96f7-b525be608bd5
-- title:
--   Extend odd exact-support dual solutions to all support sizes
-- statement:
--   Assume logarithmic-cost exact-support adversary solutions are available for every odd cardinality at least three. Then, after increasing the universal constant, every exact cardinality $1\le r\le k$ admits a feasible solution of cost at most $C\log k$.
--
--   For even $r$, apply the paper’s one-coordinate lift to the odd size $r+1$ and restrict back to the original coordinates. The cases $r=1,2$ have constant cost, which is absorbed because $k\ge2$ and $\log k$ is bounded below by $\log2$.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Eq. (127) and Sections 4.3 and 4.5.3: one-coordinate lift for even support sizes and constant-size base cases.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem odd_exact_family_to_all_sizes : ∀ C₀ : ℝ, 0 < C₀ → (∀ n r : ℕ, 3 ≤ r → r ≤ n → Odd r → ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ, DualFeasible (fun A : ExactSupports n r => A.1) X ∧ DualCostAtMost X (C₀ * Real.log r)) → ∃ C : ℝ, 0 < C ∧ ∀ n k r : ℕ, 2 ≤ k → k ≤ n → 1 ≤ r → r ≤ k → ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ, DualFeasible (fun A : ExactSupports n r => A.1) X ∧ DualCostAtMost X (C * Real.log k) := by sorry

end QuantumLTF.Majority
