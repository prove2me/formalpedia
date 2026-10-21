-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P07_oscillatorEntropyBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P07.oscillatorEntropyBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:12:17.930882+00:00
-- url     : https://prove2.me/theorems/4b6b5fcc-7904-4d01-bdf7-5a813b3b889e
-- title:
--   Explicit multimode oscillator entropy-energy envelope
-- statement:
--   Consider an $\ell$-mode oscillator with $\ell\ge1$, $\hbar>0$, and frequencies $\omega_i>0$. Its Fock basis is indexed by all occupations $n\in\mathbb N^\ell$, with energies $\sum_i\hbar\omega_i(n_i+1/2)$. Put $E_0=\frac12\sum_i\hbar\omega_i$ and $E_\ast=(\prod_i\hbar\omega_i)^{1/\ell}$. Let $F_H(E)$ be the supremum of von Neumann entropy in nats over all normalized trace-class states with mean energy at most $E$. Then, for every $E\ge E_0$,
--
--   $$F_H(E)\le\widehat F_{\ell,\omega}(E):=\ell\log\frac{E+E_0}{\ell E_\ast}+\ell.$$
--
--   Moreover, $\widehat F_{\ell,\omega}(E)=o(\sqrt E)$ as $E\to\infty$. The envelope is continuous, strictly increasing, and strictly concave on $[0,\infty)$, twice continuously differentiable on $(0,\infty)$, with positive value and first derivative and negative second derivative there. It also satisfies $\widehat F_{\ell,\omega}(E)=o(E)$.
--
--   This provides the explicit entropy envelope used in the oscillator specializations. The admissibility properties are also stated on p.24.
-- source:
--   Uniform finite-dimensional approximation of basic capacities of energy-constrained channels, arXiv:1707.05641v2, PDF p. 9, Equation (24); properties (45),(46) on p.24

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P07

noncomputable section

open Filter

open scoped NNReal ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P07

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier30.P05 (EnergySpectrum groundEnergy)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Unnumbered oscillator bound (24), PDF p.9, and its applicability to (45),(46)
on PDF p.24. Positive mode count, Planck constant and frequencies exclude empty
products and zero denominators. The limit is condition (22), with the explicit
smooth positive increasing strictly concave envelope used in Section 4.3. -/
theorem oscillatorEntropyBound {ell : ℕ} (hell : 0 < ell)
    (b : HilbertBasis (Fin ell → ℕ) ℂ H)
    (hbar : ℝ) (hhbar : 0 < hbar) (omega : Fin ell → ℝ)
    (homega : ∀ i, 0 < omega i) :
    (∀ E : ℝ, oscillatorGround hbar omega ≤ E →
      oscillatorEntropyBounded b hbar omega E ≤ ENNReal.ofReal (oscillatorEnvelope hbar omega E)) ∧
    Tendsto (fun E : ℝ => oscillatorEnvelope hbar omega E / Real.sqrt E) atTop (nhds 0) ∧
    ContinuousOn (oscillatorEnvelope hbar omega) (Set.Ici 0) ∧
    StrictMonoOn (oscillatorEnvelope hbar omega) (Set.Ici 0) ∧
    StrictConcaveOn ℝ (Set.Ici 0) (oscillatorEnvelope hbar omega) ∧
    ContDiffOn ℝ 2 (oscillatorEnvelope hbar omega) (Set.Ioi 0) ∧
    (∀ E : ℝ, 0 < E → 0 < oscillatorEnvelope hbar omega E ∧
      0 < deriv (oscillatorEnvelope hbar omega) E ∧
      deriv (deriv (oscillatorEnvelope hbar omega)) E < 0) ∧
    Tendsto (fun E : ℝ => oscillatorEnvelope hbar omega E / E) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P07

end
