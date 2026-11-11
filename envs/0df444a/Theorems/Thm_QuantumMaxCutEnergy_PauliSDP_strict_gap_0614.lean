-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_strict_gap_0614
-- name    : QuantumMaxCutEnergy.PauliSDP.strict_gap_0614
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:02:26.665572+00:00
-- url     : https://prove2.me/theorems/a5d08185-dbcb-4818-b70c-173a43d62c7c
-- title:
--   A fixed finite Pauli relaxation with a strict gap margin above 0.614
-- statement:
--   There exist one fixed natural relaxation level $k\ge2$ and one rational constant $\gamma\in(0.614,1]$ such that, for every finite graph $G$ with nonnegative rational edge weights,
--
--   $$\gamma U_k(G)\le\mathrm{OPT}(G)\le U_k(G).$$
--
--   Both $k$ and $\gamma$ are chosen before the input graph. The value $U_k$ is the specified Pauli moment SDP, not an unspecified upper-bound function. This open target requires the spectral bound, bounded-subset exactness, the partially entangled matching analysis, and a strict-margin argument selecting a finite level. No particular value of $k$ is claimed.
-- source:
--   Apte, Parekh and Sud, public arXiv2506.03441v1, Corollary10, https://arxiv.org/html/2506.03441v1#S5.SS3 ; Bakshi, Basu, Kothari and Li, public arXiv2605.14994v1, Theorem3.1, https://arxiv.org/html/2605.14994v1#S3 ; Apte, Lee, Marwaha, Parekh and Sud, ESA2025, Algorithm3 and analysis after Eq24, https://doi.org/10.4230/LIPIcs.ESA.2025.101 . A sufficiently large fixed ordinary SoS level, rather than level2 or13, is the proposed route.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.strict_gap_0614 :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ γ : ℚ≥0,
      (0.614 : ℝ) < (γ : ℝ) ∧ (γ : ℝ) ≤ 1 ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (γ : ℝ) * QuantumMaxCutEnergy.PauliSDP.value k G ≤
          QuantumMaxCutEnergy.optimum G ∧
        QuantumMaxCutEnergy.optimum G ≤ QuantumMaxCutEnergy.PauliSDP.value k G := by sorry
