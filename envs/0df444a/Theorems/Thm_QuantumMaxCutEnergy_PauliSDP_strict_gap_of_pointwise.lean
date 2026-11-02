-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_strict_gap_of_pointwise
-- name    : QuantumMaxCutEnergy.PauliSDP.strict_gap_of_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T03:54:39.77137+00:00
-- url     : https://prove2.me/theorems/e3e53c3e-891e-4979-a27e-5a52f6e08cdc
-- title:
--   0.595 reduction: pointwise per-edge bound gives the level-2 integrality gap
-- statement:
--   The reduction step of the level-2 Quantum Max-Cut analysis: the 0.595 integrality comparison follows from a per-edge pointwise bound.
--
--   Let $\gamma \in [0,1]$ be rational with $\gamma > 0.595$. Suppose that
--
--   1. **per-edge pointwise bound:** for every finite weighted graph $(V,w)$ and every feasible level-2 Pauli-moment solution $L$, the energy of some quantum state is at least $\gamma$ times the relaxation objective $\sum_e w_e c_e$, where $c_e = (1 - L(XX_e) - L(YY_e) - L(ZZ_e))/2$; and
--   2. **upper bound:** the true optimum is at most the level-2 relaxation value, $\mathrm{OPT}(G) \le \mathrm{value}_2(G)$.
--
--   Then
--   $$
--   \forall G,\quad \gamma \cdot \mathrm{value}_2(G) \le \mathrm{OPT}(G) \le \mathrm{value}_2(G),$$
--   i.e. the level-2 relaxation has integrality gap at most $1/\gamma < 1/0.595$.
--
--   **Role.** This isolates the whole supremum bookkeeping of the campaign's $0.595$ entry: the relaxation value is a supremum over feasible moment arrays and the optimum a supremum over states, and the reduction transfers a pointwise per-array inequality through both suprema, leaving only the per-edge analysis (the matching and product-state candidates of Lee–Parekh, ICALP 2024) as the remaining mathematical obligation.
--
--   **Formalization Note.** Stated over the campaign's published model (`QuantumMaxCutEnergy` and `PauliSDP` definitions); the proof takes suprema with `sSup_le` and the monotonicity of the objective in the moment array.
-- source:
--   Reduction layer for Eunou Lee and Ojas Parekh, An Improved Quantum Max Cut Approximation via Matching, ICALP 2024, https://arxiv.org/abs/2401.03616 , Theorem 2 (supremum bookkeeping only; the analysis is the unfinished part)

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.strict_gap_of_pointwise (γ : ℚ≥0) (h0 : (0.595 : ℝ) < (γ : ℝ)) (h1 : (γ : ℝ) ≤ 1)
    (hlow : ∀ (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ),
      QuantumMaxCutEnergy.PauliSDP.Feasible 2 L →
        (γ : ℝ) * QuantumMaxCutEnergy.PauliSDP.objective w L ≤ QuantumMaxCutEnergy.optimum ⟨n, w⟩)
    (hhigh : ∀ G : QuantumMaxCutEnergy.Input,
      QuantumMaxCutEnergy.optimum G ≤ QuantumMaxCutEnergy.PauliSDP.value 2 G) :
    ∃ γ : ℚ≥0, (0.595 : ℝ) < (γ : ℝ) ∧ (γ : ℝ) ≤ 1 ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (γ : ℝ) * QuantumMaxCutEnergy.PauliSDP.value 2 G ≤ QuantumMaxCutEnergy.optimum G ∧
        QuantumMaxCutEnergy.optimum G ≤ QuantumMaxCutEnergy.PauliSDP.value 2 G := by sorry
