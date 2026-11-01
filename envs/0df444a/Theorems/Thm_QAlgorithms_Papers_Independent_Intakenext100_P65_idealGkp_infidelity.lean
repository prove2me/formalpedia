-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_idealGkp_infidelity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.idealGkp_infidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:23:39.313751+00:00
-- url     : https://prove2.me/theorems/eb4761ae-870f-4bd7-b0c0-9fa58166cc7a
-- title:
--   Ideal square and hexagonal GKP infidelity bounds
-- statement:
--   Let $0<\gamma<1$. Apply quantum-limited amplification of gain $1/(1-\gamma)$ after pure loss, followed by perfect nearest-lattice modular-displacement correction. Use the square normalizer lattice with step $\sqrt{\pi/2}$, or the triangular normalizer lattice with basis $\sqrt{\pi/\sqrt3}(1,e^{i\pi/3})$; in each case the stabilizer lattice is twice this lattice. A nearest lattice point gives the measured residual syndrome and its two integer coordinates modulo two give the logical Pauli. Fix a tie rule independently of the logical input. Integrating these four cosets against $p_\gamma(\alpha)=(1-\gamma)(\pi\gamma)^{-1}e^{-(1-\gamma)|\alpha|^2/\gamma}$ constructs a CPTP qubit channel $\mathcal E_L$. Nearest points exist and the four coset probabilities sum to one. Its squared maximally entangled overlap obeys
--
--   $$1-F_E(\mathcal E_{\rm square})<e^{-\pi(1-\gamma)/(8\gamma)},\qquad 1-F_E(\mathcal E_{\rm hex})<e^{-\pi(1-\gamma)/(4\sqrt3\gamma)}.$$
--
--   These are bounds for an ideal logical recovery. They also lower-bound an ideal optimal recovery's fidelity, but assert no physical finite-energy encoder approximation or matching asymptotic lower bound.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 20, §II B (2.2), §VII B (7.22)–(7.24): ideal GKP entanglement-infidelity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.6 (2.2), pp.20--21 (7.22)--(7.24): ideal recovered logical fidelity,
with both square (c=2) and hexagonal (c=sqrt(3)) constants. The channel is constructed
before any logical input through a fixed nearest-lattice syndrome decoder. This is
not finite-energy physical achievability and does not claim a matching lower asymptotic. -/
theorem idealGkp_infidelity (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1) :
    (∀ shape : LatticeShape,
      (∀ z : ℂ, ∀ m : ℤ × ℤ,
        ‖modularSyndrome shape z‖ ≤ ‖z - gkpNormalizerPoint shape m‖) ∧
      (∀ z : ℂ, modularSyndrome shape z ∈ correctableCell shape) ∧
      (∑ c : Fin 2 × Fin 2, cosetProbability shape g c) = 1 ∧
      IsChannel (idealRecoveredChannel shape g)) ∧
    1 - QuditFidelity.entanglementFidelity 2 (by decide) (idealRecoveredChannel .square g) <
      Real.exp (-Real.pi * (1 - g) / (8 * g)) ∧
    1 - QuditFidelity.entanglementFidelity 2 (by decide) (idealRecoveredChannel .hexagonal g) <
      Real.exp (-Real.pi * (1 - g) / (4 * Real.sqrt 3 * g)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
