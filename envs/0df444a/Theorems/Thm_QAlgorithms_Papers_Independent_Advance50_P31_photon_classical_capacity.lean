-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P31_photon_classical_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P31.photon_classical_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:10:33.106171+00:00
-- url     : https://prove2.me/theorems/4efd4cf7-3540-4903-9966-705e4a926df3
-- title:
--   Photon classical capacity and single-copy Fock measurement attainment
-- statement:
--   Let a noiseless channel carry noninteracting electromagnetic modes in a finite cavity, with $H_p=\sum_i\hbar\omega_i\widehat n_i$, where $\hbar>0$ and every retained $\omega_i>0$. The unpopulated zero-frequency mode is omitted. Let $k_B,T>0$ and $\beta=(k_BT)^{-1}$. There is no particle-number constraint and the chemical potential is zero. For each finite-particle Fock configuration $n$ set
--
--   $$
--   p(n)=Z^{-1}e^{-\beta\sum_i\hbar\omega_i n_i},\qquad
--   \bar n_i=(e^{\beta\hbar\omega_i}-1)^{-1}.
--   $$
--
--   Assume a finite positive partition sum, finite absolute Gibbs energy moment, and finite entropy. Let $E$ be this law's actual mean energy. Let $C_H(E)$ optimize Holevo information and $C_1(E)$ optimize single-copy accessible information over all countably supported ensembles whose average state has energy exactly $E$. For the orthogonal Fock ensemble $\mathcal G=\{p(n),|n\rangle\langle n|\}$,
--
--   $$
--   C_H(E)=C_1(E)=\chi(\mathcal G)=I_{\rm acc}(\mathcal G)=H(p)
--   =\sum_i\bigl[(1+\bar n_i)\log_2(1+\bar n_i)-\bar n_i\log_2\bar n_i\bigr].
--   $$
--
--   The ensemble is admissible, its average-state entropy equals $H(p)$, and Fock measurement attains the displayed information in a single copy. Every admissible competing average-state entropy is at most $H(p)$. The units are bits, with continuous zero-log terms.
--
--   This states the entropy upper bound and its saturation without adding a number constraint or a finite Fock cutoff. The quantum extension is separately deferred.
-- source:
--   Capacities of noiseless quantum channels for massive indistinguishable particles: Bosons vs. fermions, arXiv:quant-ph/0512200v3, PDF p. 7, §VII, Eqs.(41)–(45)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P31

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P31

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Countable I]

/-- PDF pp.5--7, Eqs.(41)--(45): noiseless photon classical capacity under only
an average energy equality, saturated by the countably supported orthogonal Fock
ensemble and also achievable by single-copy Fock measurement. The zero-frequency
mode is omitted; every retained mode has positive frequency. -/
theorem photon_classical_capacity
    (b : HilbertBasis BoseConfig ℂ H) (omega : ℕ → ℝ)
    (hbar kB T : ℝ) (hhbar : 0 < hbar) (hkB : 0 < kB)
    (hT : 0 < T) (homega : ∀ i, 0 < omega i)
    (hregular : GibbsRegular (boseEnergy (fun i => hbar * omega i))
      (fun _ => 0) ((kB * T)⁻¹) 0) :
    ThermalAttainment b (boseEnergy (fun i => hbar * omega i))
      (fun _ => 0) ((kB * T)⁻¹) 0 none
      (∑' i : ℕ, ENNReal.ofReal
        (boseEntropy (1 / (Real.exp ((kB * T)⁻¹ * (hbar * omega i)) - 1)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P31

end
