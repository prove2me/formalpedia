-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_direction_zbit_optimal
-- name    : QAlgorithms.Papers.Independent.Next46.P29.direction_zbit_optimal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:26:29.563152+00:00
-- url     : https://prove2.me/theorems/0b77e9aa-3ed2-426c-ad7d-9b606653baf5
-- title:
--   Maximum-posterior recovery is optimal for an equiprobable z-bit
-- statement:
--   For the actual highest-weight spin-$k/2$ token and qubit, let $\mathcal E_k$ be the normalized SU(2) encoding. Define $\mathcal D_k$ by measuring the actual total-spin sector and preparing $|0\rangle$ after plus, $|1\rangle$ after minus. It is a deterministic quantum channel. For a qubit channel $\Phi$, use exactly the equiprobable z-bit fidelity $F_z(\Phi)=\tfrac12\sum_{b=0}^1\langle b|\Phi(|b\rangle\langle b|)|b\rangle$. Every deterministic decoder $\mathcal D$ satisfies
--
--   $$F_z(\mathcal D\mathcal E_k)\le F_z(\mathcal D_k\mathcal E_k)=\frac{2k+1}{2(k+1)},\qquad F_z(\mathcal R_k\mathcal E_k)=\frac{k+1}{k+2}.$$
--
--   Here $\mathcal R_k$ is the covariant adjoint recovery. Its fidelity is strictly smaller for $k>0$; both values are $1/2$ at $k=0$. This objective is distinct from entanglement fidelity and Haar-average pure-state fidelity.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 16, §VI.B: optimal direction decoding for an equiprobable z-bit

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.16, Eq.(115) and following paragraph: maximum-posterior decoding is
optimal over all deterministic decoders for an equiprobable z-bit. The fixed
adjoint decoder is strictly suboptimal precisely for positive spin. -/
theorem direction_zbit_optimal (k : ℕ) :
    IsChannel (directionOptimal k) ∧
    (∀ D : Superop (Fin (k + 1) × Fin 2) (Fin 2), IsChannel D →
      zBitFidelity (D ∘ directionEncoding k) ≤
        zBitFidelity (directionOptimal k ∘ directionEncoding k)) ∧
    zBitFidelity (directionOptimal k ∘ directionEncoding k) =
      (2 * (k : ℝ) + 1) / (2 * (k + 1)) ∧
    zBitFidelity (directionRecovery k ∘ directionEncoding k) =
      (k + 1 : ℝ) / (k + 2) ∧
    (0 < k → zBitFidelity (directionRecovery k ∘ directionEncoding k) <
      zBitFidelity (directionOptimal k ∘ directionEncoding k)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
