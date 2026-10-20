-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_approximateErrorCorrection
-- name    : QAlgorithms.Papers.Independent.Dependency50.P21.approximateErrorCorrection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:15:45.714992+00:00
-- url     : https://prove2.me/theorems/8613c743-0ccc-4f7f-b4ff-2800db1ef948
-- title:
--   Two directions of the approximate quantum error correction criterion
-- statement:
--   Let A,B be finite-dimensional complex Hilbert spaces, let C be a subspace of A with orthogonal projector Π, let N:A→B be a quantum channel and ε∈[0,1]. Let RΠ,N be the same explicit averaged map (21) in both implications. If every normalized state ρ supported in C satisfies D(ρ∥Π)−D(N(ρ)∥N(Π))≤ε, then
--
--   $$F\bigl(\rho,(\mathcal R_{\Pi,\mathcal N}\circ\mathcal N)(\rho)\bigr)\ge 1-\frac{\varepsilon}{2}\qquad\text{for every }\rho\in S(C).$$
--
--   Conversely, if this fidelity bound holds for all code states, then
--
--   $$D(\rho\|\Pi)-D(\mathcal N(\rho)\|\mathcal N(\Pi))\le\sqrt\varepsilon\log\dim C+h_2(\sqrt\varepsilon)\qquad\text{for every }\rho\in S(C),$$
--
--   where h₂(p)=−p log p−(1−p)log(1−p) is binary entropy in nats, with the continuous endpoint convention. In particular Π has trace dim C and is not normalized. This characterizes approximate correction in terms of relative entropy loss.
--
--   **Formalization Note.** C is parametrized by its Hermitian idempotent Π and dim C is the dimension of its range. Both implications are vacuous when C=0. The entropy inequalities use the equivalent additive form.
-- source:
--   Universal recovery maps and approximate sufficiency of quantum relative entropy, arXiv:1509.07127v3, PDF p. 19, Corollary 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P21

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the named interfaces from the pinned accepted paper library.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- Corollary 5.1, PDF p.19, Eqs.(114)-(116): both directions with the same explicit
universal map. A codespace is parametrized by its Hermitian idempotent Pi; its dimension
is the rank of Pi. Pi is unnormalized. On supported states the entropies are finite, so
the additive inequalities are exactly the printed entropy-difference inequalities.
The zero codespace has no density operators; both implications are then vacuous. -/
theorem approximateErrorCorrection {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Pi : Mat I)
    (hPiHermitian : Pi.IsHermitian) (hPiIdempotent : Pi * Pi = Pi)
    (N : Superop I J) (hN : IsChannel N) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon ∧ epsilon ≤ 1) :
    ((∀ rho : Mat I, IsDensityMatrix rho → IsSupported rho Pi →
        relativeEntropy rho Pi ≤ relativeEntropy (N rho) (N Pi) + (epsilon : EReal)) →
      ∀ rho : Mat I, IsDensityMatrix rho → IsSupported rho Pi →
        1 - epsilon / 2 ≤ rootFidelity rho (recovery Pi N (N rho))) ∧
    ((∀ rho : Mat I, IsDensityMatrix rho → IsSupported rho Pi →
        1 - epsilon / 2 ≤ rootFidelity rho (recovery Pi N (N rho))) →
      ∀ rho : Mat I, IsDensityMatrix rho → IsSupported rho Pi →
        relativeEntropy rho Pi ≤ relativeEntropy (N rho) (N Pi) +
          ((Real.sqrt epsilon * Real.log (Module.finrank ℂ (LinearMap.range Pi.mulVecLin)) +
            Real.binEntropy (Real.sqrt epsilon) : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P21

end
