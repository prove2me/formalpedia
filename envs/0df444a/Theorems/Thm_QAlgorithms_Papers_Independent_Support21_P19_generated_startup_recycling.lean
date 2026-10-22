-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_generated_startup_recycling
-- name    : QAlgorithms.Papers.Independent.Support21.P19.generated_startup_recycling
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T05:13:40.240994+00:00
-- url     : https://prove2.me/theorems/e92fffd2-6913-4cba-a597-17360e67e06d
-- title:
--   Generated startup and exact sequential half-rate recycling
-- statement:
--   A supporting consequence of the paper's exact primitive protocols is the following pair of sequential families. For every integer $m\ge0$,
--
--   $$
--   (2m+1)[q\to qq]\ge m[q\to q]+(m+1)[qq],
--   \qquad m[q\to q]+m[qq]\ge2m[q\to qq].
--   $$
--
--   The first family uses exactly zero externally supplied entanglement: one counted cobit prepares the startup EPR pair, which is recycled through the subsequent coherent teleportations. The second consumes precisely the displayed $m$ EPR pairs and borrows no additional seed. Both families are exact on arbitrary inputs and references. In particular, for every $\delta>0$ and all sufficiently large cobit budgets $n$, there are integers $m,e_o\ge n(1/2-\delta)$ such that $n$ cobits, with zero external EPR input, simulate $m$ forward qubits and $e_o$ decoupled EPR pairs exactly. These families expose the requested sequential half-rate interface with uniform zero error.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 2, Primitive entanglement generation, coherent teleportation and Eq. (1)

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1–3, supporting consequence of cobit entanglement generation, coherent
teleportation, and Eq. (1): explicit sequential startup/recycling, with zero external seed.
The forward schedule first spends one cobit to generate the startup EPR pair, then recycles
one returned pair through m coherent teleportations. The reverse schedule consumes the
m displayed EPR pairs, with no additional borrowed pairs. Exact means uniform zero error.
This supporting statement is included for the specifically requested dependency interface. -/
theorem generated_startup_recycling :
    (∀ m : ℕ, Exact (cobitChannel 2) (budget (2*m+1) 0 0 0 0 0 0 0)
      (tensorResources (resourceTensorCopies (qubitChannel 2) m) (resourceTensorCopies (entangled 2) (m+1)))) ∧
    (∀ m : ℕ, Exact (idle 1 1) (budget 0 m m 0 0 0 0 0) (resourceTensorCopies (cobitChannel 2) (2*m))) ∧
    (∀ delta > 0, ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0, ∃ m eo : ℕ,
      (n : ℝ)*(1/2-delta) ≤ m ∧ (n : ℝ)*(1/2-delta) ≤ eo ∧
      Exact (cobitChannel 2) (budget n 0 0 0 0 0 0 0)
        (tensorResources (resourceTensorCopies (qubitChannel 2) m) (resourceTensorCopies (entangled 2) eo))) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
