-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theorem1_5
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theorem1_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:10:36.019854+00:00
-- url     : https://prove2.me/theorems/6e528550-d8ae-429d-9940-55bb9c570d4b
-- title:
--   Long-time capacity formulas from the actual peripheral blocks
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Choose the actual peripheral decomposition $\chi(\Phi)=0\oplus\bigoplus_{k=1}^K (M_{a_k}(\mathbb C)\otimes\rho_k)$, where $K\ge1$, $a_k\ge1$, and every $\rho_k$ is a positive definite density matrix on a positive-dimensional cofactor. Here $\chi(\Phi)$ is the span of eigenoperators with eigenvalues of modulus one. The summands are embedded isometrically on mutually orthogonal subspaces of the physical system.
--
--   Such a decomposition exists, and for every such decomposition,
--
--   $$
--   \lim_{n\to\infty}C_0(\Phi^n)=\log_2\sum_{k=1}^K a_k,\qquad
--   \lim_{n\to\infty}Q_0(\Phi^n)=\log_2\max_{1\le k\le K}a_k.
--   $$
--
--   The formulas distinguish the classical sum of usable block sizes from the largest quantum block.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 4, Theorem 1.5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Theorem 1.5, PDF pp.3–4: the actual peripheral decomposition, with the classical
sum and quantum maximum kept distinct. Existence is supplied by eq.(3), p.3. -/
theorem theorem1_5 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi) :
    Nonempty (PeripheralDecomposition Phi) ∧
    ∀ D : PeripheralDecomposition Phi,
      Tendsto (fun n : ℕ => classicalCapacity (Nat.iterate Phi n)) atTop
        (nhds (Real.logb 2 (peripheralBlockDimensionSum D))) ∧
      Tendsto (fun n : ℕ => quantumCapacity (Nat.iterate Phi n)) atTop
        (nhds (Real.logb 2 (blockMaximum D))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
