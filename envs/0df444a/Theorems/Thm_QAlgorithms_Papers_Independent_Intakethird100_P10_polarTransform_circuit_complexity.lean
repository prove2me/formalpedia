-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_polarTransform_circuit_complexity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.polarTransform_circuit_complexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:40:02.872406+00:00
-- url     : https://prove2.me/theorems/56433530-aba5-465a-866a-4ba7d15bd317
-- title:
--   Exact polar transform with O(N log N) CNOT/SWAP gates
-- statement:
--   For $N=2^n$, let $G_N=B_NF_2^{\otimes n}$ over $\mathbb F_2$, acting on row bit vectors. There is a family $C_n$ of circuits consisting of CNOT and SWAP gates, together with an absolute constant $C>0$ and an integer $n_0$, such that
--
--   $$
--   C_n|u\rangle=|uG_N\rangle\quad\text{for every }n,u,\qquad
--   \operatorname{size}(C_n)\le C\,2^n n\quad(n\ge n_0).
--   $$
--
--   The action is extended linearly to superpositions, and circuit size is the actual gate-list length. At $n=0$, the one-wire circuit is empty. The bound counts the polar transform; complete encoder phase preparation is a separate node.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 3, §II/IV, unnumbered complexity of the polar transform

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF pp.3,7: the transform has an exact CNOT/SWAP implementation and O(N log N)
elementary gates. One absolute constant and one eventual threshold precede n.
At n=0, N=1 and the circuit is empty. This counts no phase-preparation gates. -/
theorem polarTransform_circuit_complexity :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ,
      ∃ circuits : (n : ℕ) → List (PolarGate (2 ^ n)),
        circuits 0 = [] ∧
        (∀ n, circuitOperator (circuits n) = polarOperator n) ∧
        (∀ n, n0 ≤ n → ((circuits n).length : ℝ) ≤ C * ((2 : ℝ) ^ n) * (n : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
