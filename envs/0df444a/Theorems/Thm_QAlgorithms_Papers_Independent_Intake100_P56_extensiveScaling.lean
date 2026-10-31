-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P56_extensiveScaling
-- name    : QAlgorithms.Papers.Independent.Intake100.P56.extensiveScaling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:55:36.796791+00:00
-- url     : https://prove2.me/theorems/11705321-b132-4611-9dda-9f198966a393
-- title:
--   Quarter-log rocket-input scale of the guaranteed private and quantum violations
-- statement:
--   Let d be an integer at least 9. The random phase coupling channel R_d has two d-dimensional input registers. It independently samples Haar unitaries U,V, applies the controlled phase P after U tensor V, sends the first quantum output to Bob and the second to Eve, and gives both parties the classical descriptions. Encoders precede the random labels, which are independent across channel uses. Let E_d be the independent whole-register probability-1/2 erasure channel, with both complementary flags. Let P and Q denote unassisted operational private and quantum capacities, measured in bits and qubits per product-channel use, respectively.
--
--   Define
--
--   $$\Delta_d^P=P(R_d\otimes E_d)-P(R_d)-P(E_d),\qquad \Delta_d^Q=Q(R_d\otimes E_d)-Q(R_d)-Q(E_d).$$
--
--   Writing $L_d=\tfrac12\log_2d-2$, the statement is
--
--   $$\Delta_d^P\ge L_d,\qquad \Delta_d^Q\ge L_d,\qquad \lim_{d\to\infty}\frac{L_d}{\log_2(d^2)}=\tfrac14.$$
--
--   The dimension convention is D=d^2, the rocket input dimension. These are achievable lower-bound scales, with no exact value asserted for either actual violation or the source's unproved optimality conjecture.
-- source:
--   Extensive nonadditivity of privacy, arXiv:0904.4050v2, PDF p. 4, Discussion: magnitude

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P56

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intake100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Finite matrix-valued decoders use the Borel measurable space of their usual
entrywise topology. This supplies the measurable codomains in all code fields. -/
local instance (I J : Type) : MeasurableSpace (Matrix I J ℂ) := borel _

variable {A B E S : Type} [Fintype A] [Fintype B] [Fintype E]

variable [DecidableEq A] [DecidableEq B] [DecidableEq E] [MeasurableSpace S]

/-- Discussion, PDF p.4: both guaranteed private and quantum additivity
violations have the quarter-log rocket-input scale D=d^2. This asserts a
lower-bound scale, not an exact capacity formula or the paper's unproved
optimality conjecture. -/
theorem extensiveScaling :
    (∀ d : ℕ, 9 ≤ d →
      guaranteedViolation d ≤
        publicLabelPrivateCapacity (jointDilation d) (rocketLaw d) -
          (publicLabelPrivateCapacity (rocketDilation d) (rocketLaw d) +
            publicLabelPrivateCapacity (halfErasureDilation d) (Measure.dirac ())) ∧
      guaranteedViolation d ≤
        publicLabelQuantumCapacity (jointDilation d) (rocketLaw d) -
          (publicLabelQuantumCapacity (rocketDilation d) (rocketLaw d) +
            publicLabelQuantumCapacity (halfErasureDilation d) (Measure.dirac ()))) ∧
    Tendsto guaranteedFraction atTop (nhds (1 / 4 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P56

end
