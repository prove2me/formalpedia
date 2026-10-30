-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_decoupling_implies_merging
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.decoupling_implies_merging
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:32:44.092642+00:00
-- url     : https://prove2.me/theorems/f77dd60e-3d01-4ae5-87bb-616606da027c
-- title:
--   Weighted decoupling gives a merging protocol
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. A merging protocol is an actual adaptive finite LOCC map, with free classical communication, from Alice and Bob to the prescribed output registers. It acts as the identity on the inaccessible reference $R$. Its input is $\lvert\psi\rangle_{ABR}\otimes\lvert\Phi_K\rangle_{A_0B_0}$ and its full ideal output is $\lvert\psi\rangle_{B^{\prime}BR}\otimes\lvert\Phi_L\rangle_{A_1B_1}$, where $B^{\prime}$ is a fixed copy of $A$ and $K,L$ are positive natural Schmidt ranks. Its error is the full trace norm of actual output minus that entire pure target; its signed cost is $\log_2K-\log_2L$. Let $\psi_{ABR}$ be normalized and let $\{M_j:AA_0\to A_1\}_j$ be a complete measurement, with $\sum_jM_j^{\dagger}M_j=I$, $\dim A_1=L$. For each positive-probability outcome $j$, let $p_j$ be its actual probability and $\rho^j_{A_1R}$ its normalized marginal; let $\rho_R$ be the original reference marginal and $\tau_{A_1}=I/L$. If $\epsilon\ge0$ and
--
--   $$
--   \sum_jp_j\left\|\rho^j_{A_1R}-\tau_{A_1}\otimes\rho_R\right\|_1\le\epsilon,
--   $$
--
--   then there exists a merging protocol with the same resource ranks $K,L$ and full error at most $2\sqrt\epsilon$. Zero-probability branches contribute zero and need no normalization.
--
--   This is a sufficient operational condition on Alice’s actual measurement.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 17, Proposition 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 4.3, PDF pp.17--18, (4.5): complete Alice measurement suffices for merging.
Correction to preliminary (4.3): Bob keeps B0, as required by the purification proof.
Subnormalized branches implement the weighted sum and impose no equation at p_j=0. -/
theorem decoupling_implies_merging {A B R X : Type}
    [Fintype A] [Fintype B] [Fintype R] [Fintype X]
    [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi)
    (K L : ℕ) (hK : 0 < K) (hL : 0 < L)
    (M : X → Matrix (Fin L) (A × Fin K) ℂ)
    (hcomplete : ∑ x, (M x)ᴴ * M x = 1)
    (eps : ℝ) (heps : 0 ≤ eps) (hdecouple : decouplingSum psi K L M ≤ eps) :
    ∃ protocol : Superop ((A × Fin K) × (B × Fin K)) (Fin L × ((A × B) × Fin L)),
      Merges psi K L protocol (2 * Real.sqrt eps) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
