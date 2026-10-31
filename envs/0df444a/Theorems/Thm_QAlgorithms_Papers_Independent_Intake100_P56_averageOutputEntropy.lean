-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P56_averageOutputEntropy
-- name    : QAlgorithms.Papers.Independent.Intake100.P56.averageOutputEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:52:52.970326+00:00
-- url     : https://prove2.me/theorems/8324b02e-3d58-4ace-a898-2d68c37ec389
-- title:
--   Lemma 1: average output entropy
-- statement:
--   Let $d$ be a positive integer. The random phase coupling channel $R_d$ has two inputs $A_1,A_2\cong\mathbb C^d$. It independently samples Haar unitaries $U,V$, applies $W_{UV}=P(U\otimes V)$, where $P|i,j\rangle=e^{2\pi\mathrm{i}\,ij/d}|i,j\rangle$, and sends the first quantum output $B$ to Bob and the second $E$ to the environment. Both receive classical descriptions of $U,V$; Alice learns neither before encoding. Different uses have independent samples. All states are normalized, and all logarithms and capacities use base two.
--
--   For $d\ge9$ and an integer $n\ge0$, let $|\psi\rangle$ be any unit vector on $(A_1\otimes A_2)^{\otimes n}$, allowing arbitrary entanglement across uses. For the sampled tuples $\mathbf U,\mathbf V$, let $\rho_{\mathbf U\mathbf V}$ be Bob's quantum output after applying the corresponding conditional channels and tracing all environment registers. If $S$ denotes von Neumann entropy in bits, then
--
--   $$\mathbb E_{\mathbf U,\mathbf V}S(\rho_{\mathbf U\mathbf V})\ge n(\log_2d-2).$$
--
--   This is the pure-input block entropy bound used in the classical-capacity argument. At $n=0$ the output is the scalar density matrix with entropy zero.
-- source:
--   Extensive nonadditivity of privacy, arXiv:0904.4050v2, PDF p. 2, Lemma 1

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

/-- Lemma 1, PDF pp.2–3: average entropy for every normalized pure block input,
including inputs entangled across all uses; n=0 is the scalar case. -/
theorem averageOutputEntropy (d n : ℕ) (hd : 9 ≤ d)
    (psi : EuclideanSpace ℂ (Fin n → Fin d × Fin d)) (hpsi : IsState psi) :
    (n : ℝ) * (Real.logb 2 d - 2) ≤
      ∫ s : Fin n → RocketLabel d,
        vnEntropy (conditionalBlockMap (conditionalReceiver (rocketDilation d)) s (pureDensity psi))
          ∂Measure.pi (fun _ : Fin n => rocketLaw d) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P56

end
