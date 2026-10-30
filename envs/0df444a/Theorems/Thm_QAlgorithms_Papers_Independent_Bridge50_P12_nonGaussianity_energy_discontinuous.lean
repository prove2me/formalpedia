-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_nonGaussianity_energy_discontinuous
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.nonGaussianity_energy_discontinuous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:33:55.454958+00:00
-- url     : https://prove2.me/theorems/ceea1edb-a26a-40b6-b573-b8ff91efb478
-- title:
--   Energy-bounded discontinuity of relative entropy non-Gaussianity
-- statement:
--   Fix a one-mode oscillator Hamiltonian $H=\hbar\omega a^\dagger a$ with $\hbar\omega>0$ on the full completed Fock space. Let $\delta(\rho)=\inf_{\tau\in\mathcal G}D(\rho\Vert\tau)$, where $\mathcal G$ contains all displaced Gaussian density operators and relative entropy is extended-valued and measured in bits. There exist a finite $E>0$ and $\epsilon>0$ such that, for every $0<\epsilon'\le1$, there are density operators $\rho,\sigma$ with finite $\delta(\rho),\delta(\sigma)$ and
--
--   $$\operatorname{Tr}(H\rho),\operatorname{Tr}(H\sigma)\le E,\qquad \tfrac12\|\rho-\sigma\|_1\le\epsilon',\qquad |\delta(\rho)-\delta(\sigma)|>\epsilon.$$
--
--   This is the source counterexample to continuity under a fixed positive energy budget, with no Fock cutoff or infinite entropy subtraction.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 5, Theorem S23: energy-bounded non-Gaussianity discontinuity

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF pp.22–23, Theorem S23, S133–S134 (main discussion p.5).
The Hamiltonian is given; the positive finite budget and separation precede the
accuracy. Witnesses have finite non-Gaussianity, making the real difference
meaningful. States live on the full completed one-mode Fock space. -/
theorem nonGaussianity_energy_discontinuous (hw : ℝ) (hhw : 0 < hw) :
    ∃ E : ℝ, 0 < E ∧ ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ epsilon2 : ℝ, 0 < epsilon2 → epsilon2 ≤ 1 →
      ∃ rho sigma : QAlgorithms.Papers.Independent.Dependency50.P33.State (Fin 1 → ℕ),
        oscillatorEnergyExpectation hw rho.coefficients ≤ ENNReal.ofReal E ∧
        oscillatorEnergyExpectation hw sigma.coefficients ≤ ENNReal.ofReal E ∧
        QAlgorithms.Papers.Independent.Dependency50.P33.traceSize
          (rho.coefficients - sigma.coefficients) / 2 ≤ ENNReal.ofReal epsilon2 ∧
        nonGaussianity rho ≠ ⊤ ∧ nonGaussianity sigma ≠ ⊤ ∧
        epsilon < |(nonGaussianity rho).toReal - (nonGaussianity sigma).toReal| := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
