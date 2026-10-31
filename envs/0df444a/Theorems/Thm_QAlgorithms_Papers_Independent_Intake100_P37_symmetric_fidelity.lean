-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_symmetric_fidelity
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.symmetric_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:09:48.703242+00:00
-- url     : https://prove2.me/theorems/7c9083a2-8b62-4fc0-a6cd-f36d74382122
-- title:
--   Relative frequency and sampled single-particle fidelity
-- statement:
--   Let $M\ge1$, let $\rho$ be any positive trace-one $M$-qubit density invariant under every exchange of two sites, and let $\psi$ be normalized. Write $\rho_k$ for its $k$th one-qubit reduction. Then, for every site $k$,
--
--   $$
--   \frac1M\sum_{j=1}^M\langle\psi|\rho_j|\psi\rangle
--   =\langle\psi|\rho_k|\psi\rangle.
--   $$
--
--   No Bose-support assumption is needed for this equality. Separately, the normalized photon-occupation embedding is an isometry whose range is exactly the qubit vectors fixed by every site permutation. For any positive trace-one photon occupation density $\sigma$, its embedded density is positive, trace one and exchange invariant. Its photon relative frequency therefore equals the fidelity of any sampled qubit marginal. In polarization 1 the relative frequency is
--
--   $$
--   \sum_{j=0}^M\sigma_{jj}\frac{M-j}{M}.
--   $$
--
--   The diagonal entries are real for these densities. This identifies physical single-spatial-mode photon fidelity with the usual sampled-clone fidelity, without conflating swap invariance of arbitrary mixed states with support in the Bose subspace.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 7, Sec. IV, Eqs.(27)-(30); p.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7-8 Eqs.(27)-(30): exchange-invariant mixed densities have equal
single-site and average fidelities. Bose support is used only for the separate
photon occupation identification, not imposed on all exchange-invariant rho. -/
theorem symmetric_fidelity (M : ℕ) (hM : 1 ≤ M) :
    (∀ rho : Matrix (Qubits M) (Qubits M) ℂ,
      IsDensityMatrix rho → ExchangeInvariant M rho →
      ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        ∀ k : Fin M, meanCloneFidelity M rho psi = effectProb (pureDensity psi) (QAlgorithms.Papers.Independent.Support21.P18.siteReduction rho k)) ∧
    (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M)ᴴ * QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M = 1 ∧
    (∀ v : EuclideanSpace ℂ (Qubits M),
      (∀ pi : Equiv.Perm (Fin M), ∀ x : Qubits M, v (x ∘ pi) = v x) ↔
        ∃ w : EuclideanSpace ℂ (Fin (M + 1)), v = applyMatrix (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M) w) ∧
    (∀ rho : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ, IsDensityMatrix rho →
      IsDensityMatrix (photonDensity M rho) ∧
      ExchangeInvariant M (photonDensity M rho) ∧
      (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        ∀ k : Fin M, photonFrequency M rho psi =
          effectProb (pureDensity psi) (photonSample M rho k)) ∧
      photonFrequency M rho (ket (0 : Fin 2)) =
        ∑ j : Fin (M + 1), (rho j j).re * ((M - j.val : ℕ) : ℝ) / M) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
