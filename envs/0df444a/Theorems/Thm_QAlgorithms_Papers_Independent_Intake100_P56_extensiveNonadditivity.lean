-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P56_extensiveNonadditivity
-- name    : QAlgorithms.Papers.Independent.Intake100.P56.extensiveNonadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:52:04.040126+00:00
-- url     : https://prove2.me/theorems/39189cd6-45f8-4cd6-92e5-aa7dd4ad9524
-- title:
--   Extensive nonadditivity of private capacity
-- statement:
--   Let $d$ be a positive integer. The random phase coupling channel $R_d$ has two inputs $A_1,A_2\cong\mathbb C^d$. It independently samples Haar unitaries $U,V$, applies $W_{UV}=P(U\otimes V)$, where $P|i,j\rangle=e^{2\pi\mathrm{i}\,ij/d}|i,j\rangle$, and sends the first quantum output $B$ to Bob and the second $E$ to the environment. Both receive classical descriptions of $U,V$; Alice learns neither before encoding. Different uses have independent samples. All states are normalized, and all logarithms and capacities use base two.
--
--   Let $\mathcal E_d$ erase an entire $d$-dimensional register with probability $1/2$, with an orthogonal flag, independently of the rocket channel. Write $P(N)$ for unassisted private classical capacity per use, with the full channel environment available to the eavesdropper. For every $d\ge9$,
--
--   $$P(R_d)<2,\qquad P(\mathcal E_d)=0,\qquad P(R_d\otimes\mathcal E_d)\ge\tfrac12\log_2 d.$$
--
--   These bounds exhibit private-capacity violations growing proportionally to the logarithm of the rocket input dimension $d^2$. A product-channel use consists of one call to each factor. Public continuous labels are handled by conditional finite-dimensional states and averages.
-- source:
--   Extensive nonadditivity of privacy, arXiv:0904.4050v2, PDF p. 1, Main result

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

/-- Main synthesis, abstract and PDF pp.1–3. Private capacity below two bits,
zero private half-erasure capacity, and a joint private capacity at least half log d.
The strict inequality uses the sharper entropy estimate printed on p.3. -/
theorem extensiveNonadditivity (d : ℕ) (hd : 9 ≤ d) :
    publicLabelPrivateCapacity (rocketDilation d) (rocketLaw d) < 2 ∧
    publicLabelPrivateCapacity (halfErasureDilation d) (Measure.dirac ()) = 0 ∧
    (1 / 2 : ℝ) * Real.logb 2 d ≤
      publicLabelPrivateCapacity (jointDilation d) (rocketLaw d) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P56

end
