-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P31_high_temperature_fermionic_advantage
-- name    : QAlgorithms.Papers.Independent.Advance50.P31.high_temperature_fermionic_advantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:07:47.984223+00:00
-- url     : https://prove2.me/theorems/c03e0169-63e9-443e-a0e1-2719fb5d79ce
-- title:
--   High-temperature fermionic advantage in a power-law trap
-- statement:
--   Consider the continuum thermodynamic model of a noiseless channel carrying massive, indistinguishable, noninteracting spinless particles in the power-law potential $V(x)=|x|^\gamma$ in a positive integer dimension $d$. Let $\gamma,A,k_B,N>0$, put $a=d/\gamma+d/2$, and use the common semiclassical density of states $\rho(\epsilon)=A\epsilon^{a-1}$ for $\epsilon>0$. Assume $1/\gamma+1/2>1/d$, equivalently $a>1$.
--
--   At temperature $T>0$, set $\beta=(k_BT)^{-1}$. Solve the Bose and Fermi fugacities separately at the same mean particle number $N$: their occupations are $n_b(\epsilon)=z_b/(e^{\beta\epsilon}-z_b)$ and $n_f(\epsilon)=z_f/(e^{\beta\epsilon}+z_f)$. Above condensation the respective number integrals equal $N$; in the condensed Bose regime $z_b=1$ and the excess number occupies the zero-energy condensate, contributing no entropy in this continuum model. Define the classical thermodynamic capacities by integrating $(1+n_b)\log_2(1+n_b)-n_b\log_2 n_b$ and $-n_f\log_2n_f-(1-n_f)\log_2(1-n_f)$ against $\rho(\epsilon)d\epsilon$. Then
--
--   $$
--   \exists T_0>0\;\forall T\ge T_0,\qquad C_b(T,N)<C_f(T,N).
--   $$
--
--   The comparison fixes the trap, temperature, and mean particle number, while allowing different chemical potentials and energies. It gives an eventual high-temperature advantage in the continuum model, with no numerical moderate-temperature threshold.
-- source:
--   Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions, arXiv:quant-ph/0512200v3, PDF p. 12, §IX, Theorem, Eq.(61)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P31

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Countable I]

/-- PDF p.12, Theorem (61), continuum reading established on p.14, Eqs.(83)--(90).
For the same spinless, noninteracting power-law trap, temperature, and positive
mean N, fermionic classical thermodynamic capacity is strictly greater eventually.
The positive normalization A includes the common mass. The theorem gives no
numerical moderate-temperature interval and makes no exact discrete-spectrum claim. -/
theorem high_temperature_fermionic_advantage
    (d : ℕ) (hd : 0 < d) (gamma A kB N : ℝ)
    (hgamma : 0 < gamma) (hA : 0 < A) (hkB : 0 < kB) (hN : 0 < N)
    (hpower : 1 / gamma + 1 / 2 > 1 / (d : ℝ)) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, T0 ≤ T →
      thermodynamicCapacity false A (trapExponent d gamma) kB N T <
        thermodynamicCapacity true A (trapExponent d gamma) kB N T := by sorry

end QAlgorithms.Papers.Independent.Advance50.P31

end
