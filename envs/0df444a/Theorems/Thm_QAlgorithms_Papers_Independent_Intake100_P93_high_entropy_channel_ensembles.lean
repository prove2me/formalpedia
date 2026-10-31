-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_high_entropy_channel_ensembles
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.high_entropy_channel_ensembles
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:46:44.359665+00:00
-- url     : https://prove2.me/theorems/f90c8f02-4a65-4332-9dc0-176fab68dc9f
-- title:
--   §VII: high-entanglement ensembles of unital and general channel states
-- statement:
--   For a unital channel on a nonzero $d$-dimensional system and its normalized Choi state $\rho_T$, every $\epsilon,\delta>0$ and all sufficiently large positive integers $n$ admit a normalized pure-state ensemble with average $\omega_n$ such that
--
--   $$\|\omega_n-\rho_T^{\otimes n}\|_1\le\epsilon,\qquad E(\varphi_j)\ge n(\log_2d-\delta)\quad\text{for every component }j.$$
--
--   More generally, let $\varphi^{RA}$ be any normalized finite-dimensional pure input, let $T:A\to B$ be a channel, and set $\rho=(\mathrm{id}_R\otimes T)\varphi$. There are local subspaces of dimensions $D_R,D_B$ with $|\log_2D_R-nS(R)|\le n\delta$ and $|\log_2D_B-nS(B)|\le n\delta$, for which the normalized projected state is within trace norm $\epsilon$ of $\rho^{\otimes n}$. On these subspaces it is within trace norm $\epsilon$ of a pure ensemble whose every component has entanglement at least $n(\min\{S(R),S(B)\}-\delta)$. The subspaces are represented by actual local isometric embeddings and the projection weight is positive. This states the entropy-only consequence, without asserting closeness of the components to maximally entangled kets or approximating the channel in norm.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 9, §VII: high-entanglement ensembles of unital and general channel states

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF p.9, Section VII: both stated entropy-only ensemble consequences.
The general source is arbitrary normalized phi, and includes the effective
local dimensions and discarded-subspace approximation. No cb-norm statement,
full-input isometry, or componentwise maximally-entangled fidelity is inferred. -/
theorem high_entropy_channel_ensembles :
    (∀ d : ℕ, 0 < d → ∀ T : Superop (Fin d) (Fin d), IsChannel T → T 1 = 1 →
      ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ, N < n →
        HighEntropyEnsemble (choiState T) n (Real.logb 2 d) epsilon delta) ∧
    (∀ r a b : ℕ, 0 < r → 0 < a → 0 < b →
      ∀ T : Superop (Fin a) (Fin b), IsChannel T →
      ∀ phi : EuclideanSpace ℂ (Fin r × Fin a), ‖phi‖ = 1 →
      ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ, N < n →
        TypicalHighEntropyEnsemble (idTensorSuperop T (pureDensity phi)) n epsilon delta) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
