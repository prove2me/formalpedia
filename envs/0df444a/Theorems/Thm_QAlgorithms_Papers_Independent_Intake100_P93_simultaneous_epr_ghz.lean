-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_simultaneous_epr_ghz
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.simultaneous_epr_ghz
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:36:07.632784+00:00
-- url     : https://prove2.me/theorems/7813a3ec-944c-4ffe-af52-c12c2bc23897
-- title:
--   Theorem 2: simultaneous EPR and GHZ distillation
-- statement:
--   Let $\psi^{ABC}$ be a normalized finite-dimensional pure state and let $\{q_j,|\psi_j\rangle^{AB}\}$ be any finite normalized pure-state ensemble of its actual marginal $\psi^{AB}$. Put $\bar E=\sum_jq_jS(\psi_j^A)$ and $\chi=\min\{S(A),S(B)\}-\bar E$, with entropy in bits. For every $\epsilon,\delta>0$, all sufficiently large positive integers $n$ admit nonnegative integer counts $g,e$ and a protocol consisting of one instrument at $C$, one broadcast, and message-dependent local channels at $A$ and $B$, such that
--
--   $$g\ge n(\chi-\delta),\qquad e\ge n(\bar E-\delta),\qquad F\bigl(\rho_{\rm out},\Gamma^{\otimes g}\otimes\Phi_2^{\otimes e}\bigr)\ge1-\epsilon.$$
--
--   Here $\Gamma=(|000\rangle+|111\rangle)/\sqrt2$ and $\Phi_2=(|00\rangle+|11\rangle)/\sqrt2$, the latter shared by $A,B$. There is no feedback or $A$–$B$ communication. The helper may enlarge its space locally. The single fidelity test concerns the entire joint target. This gives a simultaneous distillation tradeoff rather than two separate marginal guarantees.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 2, Theorem 2: simultaneous EPR and GHZ distillation

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

/-- PDF pp.2,5--6, Theorem 2: simultaneous joint-output distillation for every
pure ensemble of the actual marginal. The helper may locally enlarge its
space. PureEnsemble entanglement is computed, not assumed as an independent rate. -/
theorem simultaneous_epr_ghz {d : Fin 3 → ℕ} (hd : ∀ i, 0 < d i)
    (psi : EuclideanSpace ℂ (AssistanceBasis d)) (hpsi : ‖psi‖ = 1)
    (ens : PureEnsemble (Fin (d 0) × Fin (d 1)))
    (hens : Information100.P08.pureAverage ens = pairMarginal (pureDensity psi) 0 1) :
    ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∃ g e : ℕ,
        (min (partyEntropy (pureDensity psi) {0}) (partyEntropy (pureDensity psi) {1}) -
          averageEntanglement ens - delta) * n ≤ g ∧
        (averageEntanglement ens - delta) * n ≤ e ∧
        DistillationBlock (pureDensity psi) (.broadcast 2) 0 1 n g e epsilon := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
