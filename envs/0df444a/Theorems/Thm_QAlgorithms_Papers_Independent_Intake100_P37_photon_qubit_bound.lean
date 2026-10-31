-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_photon_qubit_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.photon_qubit_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:10:33.742566+00:00
-- url     : https://prove2.me/theorems/f92059bf-964a-4fc1-b193-8910a6c4e671
-- title:
--   Physical photon/qubit operation equivalence and optimality bounds
-- statement:
--   Fix $1\le m\le M$. Let $E_n$ be the normalized occupation embedding of the $n$-photon space into the totally symmetric $n$-qubit space. The maps
--
--   $$
--   \widehat T(X)=E_MT(E_m^\dagger XE_m)E_M^\dagger,\qquad
--   T(X)=E_M^\dagger\widehat T(E_mXE_m^\dagger)E_M
--   $$
--
--   give inverse correspondences between photon channels and completely positive qubit maps supported on the input and output Bose corners and trace preserving on the input corner. They preserve polarization covariance. Consequently every fixed universal photon channel has, for every normalized $\psi$, relative-frequency fidelity at most
--
--   $$
--   F_{m,M}=\frac{Mm+M+m}{M(m+2)}.
--   $$
--
--   A covariant trace-nonincreasing completely positive photon map has a scalar effect: $\operatorname{Tr}T(X)=p\operatorname{Tr}X$, with $p\in[0,1]$ computed on a fixed reference input. If $p>0$, normalization by this fixed scalar yields a covariant channel. For a finite instrument with outcomes $M_j\ge m$ and total trace preservation, its branch weights sum to one and its mean fidelity is bounded by $\sum_jp_jF_{m,M_j}$. For countably many outcomes $M\ge m$ with a specified probability mass function equal to the branch weights, both expectations are absolutely convergent and the same weighted bound holds. Subnormalized branch fidelities are used, so zero-probability branches require no division. This transfers the qubit bound cited in [7] to physical photon operations.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 8, Sec. IV, final optimality argument

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8: physical photon/Bose-qubit channel equivalence transfers the
universal cloning bound. Covariant CP selected branches have a scalar success
effect, so normalization is linear. Finite and countable output counts use
the SAME probabilities to average fidelities and their M-dependent bounds. -/
theorem photon_qubit_bound (m M : ℕ) (hm : 1 ≤ m) (hMM : m ≤ M) :
    (∀ T : Superop (Fin (m + 1)) (Fin (M + 1)),
      (IsChannel T ↔ BoseChannel m M (toQubitMap m M T)) ∧
      toPhotonMap m M (toQubitMap m M T) = T ∧
      (PolarizationCovariant m M T ↔ BoseUniversal m M (toQubitMap m M T))) ∧
    (∀ S : Superop (Qubits m) (Qubits M), BoseChannel m M S →
      IsChannel (toPhotonMap m M S) ∧ toQubitMap m M (toPhotonMap m M S) = S) ∧
    (∀ T : Superop (Fin (m + 1)) (Fin (M + 1)),
      IsChannel T → PolarizationCovariant m M T →
      ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        photonFrequency M (T (pureDensity (QAlgorithms.Papers.Independent.Support21.P18.symmetricQubitKet m psi))) psi ≤ benchmark m M) ∧
    (∀ T : Superop (Fin (m + 1)) (Fin (M + 1)),
      FiniteKrausBranch T → PolarizationCovariant m M T →
      0 ≤ mapWeight m M T ∧ mapWeight m M T ≤ 1 ∧
      (∀ rho, (T rho).trace = (mapWeight m M T : ℂ) * rho.trace) ∧
      (0 < mapWeight m M T → IsChannel (normalizeMap m M T) ∧
        PolarizationCovariant m M (normalizeMap m M T))) ∧
    (∀ L : ℕ, ∀ out : Fin L → ℕ, (∀ j, m ≤ out j) →
      ∀ T : (j : Fin L) → Superop (Fin (m + 1)) (Fin (out j + 1)),
      (∀ j, FiniteKrausBranch (T j) ∧ PolarizationCovariant m (out j) (T j)) →
      (∀ rho, ∑ j, (T j rho).trace = rho.trace) →
      (∑ j, mapWeight m (out j) (T j)) = 1 ∧
      ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        (∑ j, photonFrequency (out j) (T j (pureDensity (QAlgorithms.Papers.Independent.Support21.P18.symmetricQubitKet m psi))) psi) ≤
          ∑ j, mapWeight m (out j) (T j) * benchmark m (out j)) ∧
    (∀ T : (o : {n : ℕ // m ≤ n}) → Superop (Fin (m + 1)) (Fin (o.val + 1)),
      (∀ o, FiniteKrausBranch (T o) ∧ PolarizationCovariant m o.val (T o)) →
      ∀ law : PMF {n : ℕ // m ≤ n},
      (∀ o, mapWeight m o.val (T o) = (law o).toReal) →
      ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
        Summable (fun o => (law o).toReal * benchmark m o.val) ∧
        Summable (fun o => photonFrequency o.val (T o (pureDensity (QAlgorithms.Papers.Independent.Support21.P18.symmetricQubitKet m psi))) psi) ∧
        (∑' o, photonFrequency o.val (T o (pureDensity (QAlgorithms.Papers.Independent.Support21.P18.symmetricQubitKet m psi))) psi) ≤
          ∑' o, (law o).toReal * benchmark m o.val) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
