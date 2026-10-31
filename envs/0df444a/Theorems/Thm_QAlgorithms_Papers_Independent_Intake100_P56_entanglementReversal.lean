-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P56_entanglementReversal
-- name    : QAlgorithms.Papers.Independent.Intake100.P56.entanglementReversal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:54:10.446077+00:00
-- url     : https://prove2.me/theorems/dab33b37-0a26-4b15-ae82-fa592457d6bb
-- title:
--   Exact reversal with one receiver-held Bell half
-- statement:
--   Let $d$ be a positive integer. The random phase coupling channel $R_d$ has two inputs $A_1,A_2\cong\mathbb C^d$. It independently samples Haar unitaries $U,V$, applies $W_{UV}=P(U\otimes V)$, where $P|i,j\rangle=e^{2\pi\mathrm{i}\,ij/d}|i,j\rangle$, and sends the first quantum output $B$ to Bob and the second $E$ to the environment. Both receive classical descriptions of $U,V$; Alice learns neither before encoding. Different uses have independent samples. All states are normalized, and all logarithms and capacities use base two.
--
--   Prepare the normalized maximally entangled state $|\phi_d\rangle=d^{-1/2}\sum_{j=0}^{d-1}|j,j\rangle$ on $A_2B'$, with $B'$ already at Bob. For any density matrix $\rho$ on $A_1$, let $\sigma_{UV}^{BB'}$ be the output obtained by applying $W_{UV}$ to $A_1A_2$ and tracing $E$. Define
--
--   $$D_{UV}=(U^\dagger\otimes I)P_{BB'}^\dagger\bigl(I\otimes(V^T)^\dagger\bigr).$$
--
--   For every $d\ge1$, every pair of unitaries $U,V$, and every such $\rho$,
--
--   $$\operatorname{Tr}_{B'}\bigl(D_{UV}\sigma_{UV}^{BB'}D_{UV}^\dagger\bigr)=\rho.$$
--
--   The decoder is the explicit operation in the diagram and uses public information available at the receiver. The encoder is fixed independently of that information. This identity explains the entanglement-assisted reversal.
-- source:
--   Extensive nonadditivity of privacy, arXiv:0904.4050v2, PDF p. 3, Fig. 2

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

/-- Fig.2, PDF p.3 (explained on p.2): exact, public-label-dependent recovery
with a single receiver-held Bell half. Dimension one is included. -/
theorem entanglementReversal (d : ℕ) (hd : 0 < d) (s : RocketLabel d)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    rocketRecovery d s (rocketAssistedOutput d hd s rho) = rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P56

end
