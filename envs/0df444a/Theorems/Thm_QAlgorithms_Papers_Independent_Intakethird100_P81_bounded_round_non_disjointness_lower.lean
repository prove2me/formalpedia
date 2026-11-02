-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_bounded_round_non_disjointness_lower
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.bounded_round_non_disjointness_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:02:13.544752+00:00
-- url     : https://prove2.me/theorems/6c9eaad0-cdc1-44a5-b935-fb2666dc6c7c
-- title:
--   Fixed-round quantum non-disjointness lower bound
-- statement:
--   Fix an integer $k\ge1$ independently of the input length. Alice and Bob receive $x,y\in\{0,1\}^n$ and must output one exactly when some coordinate has $x_i=y_i=1$. A quantum protocol may start with any finite normalized, input-independent prior entangled state, use arbitrary private workspace, and exchange $k$ alternating messages starting with either player. It must succeed with probability at least $2/3$ on every input; only transmitted qubits are charged.
--
--   There are constants $C_k>0$ and $n_k\ge2$ such that for all $n\ge n_k$, every such protocol has cost
--   $$
--   c\ge C_k n^{1/k}.
--   $$
--
--   The constants may depend on the fixed round count. This is the paper's non-disjointness output convention despite its notation $\mathrm{DISJ}_n$.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 19, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Theorem 4, PDF p.19: k is fixed before the positive constant and eventual threshold.
Either starter is allowed; DISJ has the source's non-disjointness output convention. -/
theorem bounded_round_non_disjointness_lower (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ (start : Party) (P : QuantumProtocol (Fin n → Bool) (Fin n → Bool) Bool),
        P.valid start k → P.computes nonDisjoint (1 / 3) →
        C * (n : ℝ) ^ (1 / (k : ℝ)) ≤ P.cost := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
