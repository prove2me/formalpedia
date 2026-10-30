-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P31_fermion_classical_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P31.fermion_classical_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:09:35.909987+00:00
-- url     : https://prove2.me/theorems/7ef35bd4-7893-4e38-80d0-a2193de411ae
-- title:
--   Spin-degenerate fermion classical capacity and corrected entropy formula
-- statement:
--   Consider a noiseless channel carrying massive, indistinguishable, noninteracting fermions with a positive integer spin degeneracy $g=2s+1$. Mode $i$ has energy $\epsilon_i$, identical for all $g$ spin labels, and the mode energies are bounded below. Each spin-resolved occupation $n_{i,\sigma}$ is zero or one. Let $k_B,T>0$, $\beta=(k_BT)^{-1}$ and $\mu_f\in\mathbb R$. On all finite-particle Fock configurations set
--
--   $$
--   p_f(n)=Z_f^{-1}\exp\!\left[-\beta\sum_{i,\sigma}(\epsilon_i-\mu_f)n_{i,\sigma}\right],\qquad
--   \bar n_i=\frac{g}{e^{\beta(\epsilon_i-\mu_f)}+1}.
--   $$
--
--   Assume a normalizable positive partition sum, finite absolute Gibbs energy and particle-number moments, and finite Shannon entropy. Let $E,N$ be the resulting means. Optimize Holevo information and single-copy accessible information over all countably supported ensembles whose average energy and number equal $E,N$, obtaining $C_H,C_1$. The fermionic number-state ensemble $\mathcal G_f=\{p_f(n),|n\rangle\langle n|\}$ is admissible and satisfies
--
--   $$
--   C_H(E,N)=C_1(E,N)=\chi(\mathcal G_f)=I_{\rm acc}(\mathcal G_f)
--   =H(p_f)=g\sum_i h_2(\bar n_i/g),
--   \quad h_2(x)=-x\log_2 x-(1-x)\log_2(1-x).
--   $$
--
--   Its average-state entropy equals $H(p_f)$, the number-state measurement attains this information in a single copy, and all competing average-state entropies are bounded by it. Entropies are in bits and zero-log terms have their continuous values.
--
--   The outside factor $g$ accounts for all independent spin states. **Source correction:** Eq.(60) prints a bosonic occupation label and a bosonic plus-sign entropy expression; the displayed formula is the unique Bernoulli-entropy correction determined by Eqs.(56),(58),(59). It does not include the separately deferred quantum-capacity equality.
-- source:
--   Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions, arXiv:quant-ph/0512200v3, PDF p. 11, §VIII B, Eqs.(56)–(60)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P31

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Countable I]

/-- PDF pp.11--12, Eqs.(56)--(60): spin-g fermion classical capacity and attaining
number-state ensemble. SOURCE CORRECTION: Eq.(60) prints bosonic nbar^b and
(1+nbar/g); Eqs.(56),(58),(59) uniquely give g*h_2(nbar^f/g), retained here
with the outside factor g. The quantum-capacity equality is not included. -/
theorem fermion_classical_capacity
    (g : ℕ) (hg : 0 < g) (b : HilbertBasis (FermiConfig g) ℂ H)
    (eps : ℕ → ℝ) (kB T mu : ℝ) (hkB : 0 < kB) (hT : 0 < T)
    (hlower : BddBelow (Set.range eps))
    (hregular : GibbsRegular (fermiEnergy (g := g) eps) (fermiNumber (g := g))
      ((kB * T)⁻¹) mu) :
    ThermalAttainment b (fermiEnergy (g := g) eps) (fermiNumber (g := g)) ((kB * T)⁻¹) mu
      (some (fockGibbsMean (fermiEnergy (g := g) eps) (fermiNumber (g := g))
        (fermiNumber (g := g)) ((kB * T)⁻¹) mu))
      ((g : ℝ≥0∞) * ∑' i : ℕ, ENNReal.ofReal
        (fermiEntropy (1 / (Real.exp ((kB * T)⁻¹ * (eps i - mu)) + 1)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P31

end
