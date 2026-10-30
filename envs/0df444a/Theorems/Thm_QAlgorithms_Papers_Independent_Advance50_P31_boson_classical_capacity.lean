-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P31_boson_classical_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P31.boson_classical_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:08:42.829662+00:00
-- url     : https://prove2.me/theorems/833314ac-cc63-4dc6-a885-6ea518c73e36
-- title:
--   Spinless-boson classical capacity and number-state attainment
-- statement:
--   Let a noiseless channel carry massive, indistinguishable, noninteracting spinless bosons in countably many modes with real energies $\epsilon_i$ bounded below. Let $k_B,T>0$, $\beta=(k_BT)^{-1}$, and $\mu_b<\inf_i\epsilon_i$. A number configuration $n=(n_i)$ has nonnegative integer occupations and finite total particle number, without a common Fock cutoff. Set $E(n)=\sum_i\epsilon_i n_i$, $\mathcal N(n)=\sum_i n_i$, and
--
--   $$
--   p_b(n)=Z_b^{-1}e^{-\beta(E(n)-\mu_b\mathcal N(n))},\qquad
--   \bar n_i=\frac{1}{e^{\beta(\epsilon_i-\mu_b)}-1}.
--   $$
--
--   Assume the partition sum is finite and positive, the Gibbs energy and number moments converge absolutely, and $H(p_b)<\infty$. Let $E$ and $N$ be the actual Gibbs means. Let $C_H(E,N)$ be the supremum of Holevo information over all countably supported quantum ensembles whose average state satisfies $\operatorname{Tr}(H\bar\rho)=E$ and $\operatorname{Tr}(\widehat N\bar\rho)=N$, and let $C_1(E,N)$ optimize their single-copy accessible information. For the orthogonal number-state ensemble $\mathcal G_b=\{p_b(n),|n\rangle\langle n|\}$,
--
--   $$
--   C_H(E,N)=C_1(E,N)=\chi(\mathcal G_b)=I_{\rm acc}(\mathcal G_b)
--   =H(p_b)=\sum_i\bigl[(1+\bar n_i)\log_2(1+\bar n_i)-\bar n_i\log_2\bar n_i\bigr].
--   $$
--
--   The ensemble is admissible, its average-state entropy is $H(p_b)$, and the number-state measurement attains that information in a single copy. Every competing average state obeying the constraints has entropy at most $H(p_b)$. All quantities are in bits, with $0\log_2 0=0$.
--
--   This gives both the optimized capacity and a concrete attaining ensemble; it asserts no Gibbs parametrization for arbitrary prescribed pairs $(E,N)$.
-- source:
--   Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions, arXiv:quant-ph/0512200v3, PDF p. 8, §VIII A.1, Eqs.(48)–(51)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P31

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Countable I]

/-- PDF pp.7--8, Eqs.(48)--(51): spinless massive boson classical capacity,
including number-state attainment and the nonasymptotic accessible-information
claim. E,N are the actual Gibbs means; existence at arbitrary E,N is not asserted. -/
theorem boson_classical_capacity
    (b : HilbertBasis BoseConfig ℂ H) (eps : ℕ → ℝ)
    (kB T mu : ℝ) (hkB : 0 < kB) (hT : 0 < T)
    (hlower : BddBelow (Set.range eps)) (hmu : mu < sInf (Set.range eps))
    (hregular : GibbsRegular (boseEnergy eps) boseNumber ((kB * T)⁻¹) mu) :
    ThermalAttainment b (boseEnergy eps) boseNumber ((kB * T)⁻¹) mu
      (some (fockGibbsMean (boseEnergy eps) boseNumber boseNumber ((kB * T)⁻¹) mu))
      (∑' i : ℕ, ENNReal.ofReal
        (boseEntropy (1 / (Real.exp ((kB * T)⁻¹ * (eps i - mu)) - 1)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P31

end
