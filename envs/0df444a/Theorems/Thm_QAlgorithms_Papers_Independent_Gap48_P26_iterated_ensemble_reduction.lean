-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_iterated_ensemble_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.iterated_ensemble_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:56:14.825261+00:00
-- url     : https://prove2.me/theorems/86bb2029-5a71-4c5c-b7b6-96d545269328
-- title:
--   Iterated path-ensemble and entropy reduction
-- statement:
--   Let $\mathcal A_\kappa$ and $\mathcal E_\eta$ be the quantum-limited channels with finite $\kappa\ge1$ and $\eta=(\kappa-1)/\kappa$, and let $\psi$ be any unit finite-energy Fock vector. For each integer $q\ge0$ there exist a nonempty countable set of labels $L\subseteq\mathbb N$, strictly positive summable weights $p_\ell$ of sum one, unit finite-energy vectors $\phi_\ell$, and bounded partial isometries $W_\ell$ preserving the supports of $\mathcal A_\kappa(|\phi_\ell\rangle\langle\phi_\ell|)$, such that
--
--   $$\mathcal E_\eta^q(|\psi\rangle\langle\psi|)=\sum_{\ell\in L}p_\ell|\phi_\ell\rangle\langle\phi_\ell|,$$
--   $$\mathcal A_\kappa(|\psi\rangle\langle\psi|)=\sum_{\ell\in L}p_\ell W_\ell\mathcal A_\kappa(|\phi_\ell\rangle\langle\phi_\ell|)W_\ell^*,$$
--   $$S(\mathcal A_\kappa(|\psi\rangle\langle\psi|))\ge\sum_{\ell\in L}p_\ell S(\mathcal A_\kappa(|\phi_\ell\rangle\langle\phi_\ell|)).$$
--
--   All coefficient series converge, all component entropies are finite, and the weighted entropy series converges. Finite ensembles are permitted. These are the jointly constructed path-ensemble identities, together with Eq. (9).
--
--   **Source correction.** Connecting partial isometries replace the printed unitaries, consistently with the correction to Eq. (6) and supporting Proposition 7 of arXiv:1312.2251v1.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 3, Eqs. (7)-(9), corrected connecting maps

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P26

open MeasureTheory Filter

open scoped ENNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Next46.P32 (NumberString vacuum)

open QAlgorithms.Papers.Independent.Next46.P45 (entanglementOfFormation)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State rankOne IsDensity IsBarycenter IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation traceClassTensorPower weylCharacteristic boundedUnitaryConjugation
   conjugateKernel partialRight GaussianDensity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3-4, (7)-(9): an existentially constructed countable path ensemble,
with finite ensembles allowed. Connecting partial isometries replace the printed
unitaries, as in arXiv:1312.2251v1, Proposition 7, PDF pp.16-17. They preserve
the entire support of each amplified component, hence preserve its entropy. -/
theorem iterated_ensemble_reduction
    (A L : Operation ℕ ℕ) (kappa : ℝ) (hk : 1 ≤ kappa)
    (hA : PhaseInsensitive A kappa (kappa - 1))
    (hL : PhaseInsensitive L ((kappa - 1) / kappa) (1 - (kappa - 1) / kappa))
    (u : Hilbert ℕ) (hu : ‖u‖ = 1) (he : weightedPhotonExpectation id (rankOne u) < ⊤)
    (q : ℕ) :
    ∃ (labels : Set ℕ), labels.Nonempty ∧
      ∃ (weight : labels → ℝ) (v : labels → Hilbert ℕ) (W : labels → B.FockOperator),
        (∀ j, 0 < weight j) ∧ Summable weight ∧ (∑' j, weight j) = 1 ∧
        (∀ j, ‖v j‖ = 1 ∧ weightedPhotonExpectation id (rankOne (v j)) < ⊤ ∧
          entropyBits (A (rankOne (v j))) < ⊤ ∧
          IsPartialIsometry (W j) ∧ PreservesSupport (W j) (A (rankOne (v j)))) ∧
        (∀ a b : ℕ,
          HasSum (fun j => (weight j : ℂ) * rankOne (v j) a b)
            ((L^[q]) (rankOne u) a b) ∧
          HasSum (fun j => (weight j : ℂ) *
            conjugateKernel (operatorCoeff (W j)) (A (rankOne (v j))) a b)
            (A (rankOne u) a b)) ∧
        entropyBits (A (rankOne u)) < ⊤ ∧
        Summable (fun j => weight j * (entropyBits (A (rankOne (v j)))).toReal) ∧
        (entropyBits (A (rankOne u))).toReal ≥
          ∑' j, weight j * (entropyBits (A (rankOne (v j)))).toReal := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
