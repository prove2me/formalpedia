-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P56_largeJointQuantumCapacity
-- name    : QAlgorithms.Papers.Independent.Intake100.P56.largeJointQuantumCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:54:53.418776+00:00
-- url     : https://prove2.me/theorems/e7ce97ec-dbd0-4da9-a310-b7e0fce63076
-- title:
--   Bell-input coherent information and joint quantum capacity
-- statement:
--   Let $d$ be a positive integer. The random phase coupling channel $R_d$ has two inputs $A_1,A_2\cong\mathbb C^d$. It independently samples Haar unitaries $U,V$, applies $W_{UV}=P(U\otimes V)$, where $P|i,j\rangle=e^{2\pi\mathrm{i}\,ij/d}|i,j\rangle$, and sends the first quantum output $B$ to Bob and the second $E$ to the environment. Both receive classical descriptions of $U,V$; Alice learns neither before encoding. Different uses have independent samples. All states are normalized, and all logarithms and capacities use base two.
--
--   Let $\mathcal E_d$ be the independent probability-$1/2$ whole-register erasure channel. Prepare $|\varphi\rangle=|\phi_d\rangle_{AA_1}|\phi_d\rangle_{B'A_2}$, where $|\phi_d\rangle=d^{-1/2}\sum_j|j,j\rangle$, and use the mixed input $\rho=\operatorname{Tr}_A|\varphi\rangle\langle\varphi|$ on $((A_1,A_2),B')$. Send $A_1A_2$ through $R_d$ and $B'$ through $\mathcal E_d$. Let $I_c(\rho,N)$ be $S(\text{Bob})-S(\text{environment})$ for this purified input, evaluated conditionally on $U,V$ and then averaged, retaining both complementary erasure flags and the discarded $E$ system. For all $d\ge1$,
--
--   $$I_c(\rho,R_d\otimes\mathcal E_d)=\tfrac12\log_2d,\qquad Q(R_d\otimes\mathcal E_d)\ge\tfrac12\log_2d.$$
--
--   Here $Q$ is unassisted operational quantum capacity. A use of the product channel includes one call to each factor, so no additional division by two is made.
-- source:
--   Extensive nonadditivity of privacy, arXiv:0904.4050v2, PDF p. 3, Large Joint Quantum Capacity

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

/-- Large Joint Quantum Capacity, PDF p.3: exact source-input coherent
information and operational capacity consequence. One use means one use of EACH
factor; the sole factor 1/2 is the erasure probability. -/
theorem largeJointQuantumCapacity (d : ℕ) (hd : 0 < d) :
    publicLabelCoherentInformation (jointDilation d) (rocketLaw d) (bellInput d) =
      (1 / 2 : ℝ) * Real.logb 2 d ∧
    (1 / 2 : ℝ) * Real.logb 2 d ≤
      publicLabelQuantumCapacity (jointDilation d) (rocketLaw d) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P56

end
