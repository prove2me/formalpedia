-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P56_smallClassicalCapacity
-- name    : QAlgorithms.Papers.Independent.Intake100.P56.smallClassicalCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:53:33.895884+00:00
-- url     : https://prove2.me/theorems/e776794f-2730-45df-a993-c63e0b1903b8
-- title:
--   Small unassisted classical capacity
-- statement:
--   Let $d$ be a positive integer. The random phase coupling channel $R_d$ has two inputs $A_1,A_2\cong\mathbb C^d$. It independently samples Haar unitaries $U,V$, applies $W_{UV}=P(U\otimes V)$, where $P|i,j\rangle=e^{2\pi\mathrm{i}\,ij/d}|i,j\rangle$, and sends the first quantum output $B$ to Bob and the second $E$ to the environment. Both receive classical descriptions of $U,V$; Alice learns neither before encoding. Different uses have independent samples. All states are normalized, and all logarithms and capacities use base two.
--
--   Let $C(R_d)$ denote the operational unassisted classical capacity: the supremum of achievable rates of reliable classical communication per use, permitting arbitrary mixed encodings entangled across an arbitrary number of uses and a joint decoding measurement depending on the public descriptions. For every $d\ge9$,
--
--   $$C(R_d)\le2.$$
--
--   Thus increasing the input dimension does not increase the channel's unassisted classical capacity beyond two bits per use. The statement includes collective encodings rather than only one-use ensembles.
-- source:
--   Extensive nonadditivity of privacy, arXiv:0904.4050v2, PDF p. 2, Small Classical Capacity

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

/-- Small Classical Capacity, PDF pp.2–3. The operational capacity includes
arbitrary entangled block encoders; this is not a one-use Holevo statement. -/
theorem smallClassicalCapacity (d : ℕ) (hd : 9 ≤ d) :
    publicLabelClassicalCapacity (rocketDilation d) (rocketLaw d) ≤ 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P56

end
