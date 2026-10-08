-- Prove2me | Theorems.Thm_WeightedMajority_Randomized_expected_mistakes_eq
-- name    : WeightedMajority.Randomized.expected_mistakes_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:13.714982+00:00
-- url     : https://prove2.me/theorems/6b4fe51c-5636-4b6d-bc8e-e7362d7c80f9
-- title:
--   §6, proof of Theorem 6.1 — the expected number of mistakes of WMR equals $\mathbf E\sum_j|\gamma^{(j)}-\rho^{(j)}|$
-- statement:
--   Consider the randomized master algorithm WMR on $t$ trials, with a pool of $n$ algorithms whose predictions $x_i^{(j)}$ lie in $[0,1]$, binary labels $\rho^{(j)}$, binary master predictions $\lambda^{(j)}$, $0 \le \beta < 1$, positive initial weights, and update factors satisfying (5.1). Let $\gamma^{(j)}$ be the weighted average prediction of the pool in trial $j$ and $m = \sum_{j=1}^t |\lambda^{(j)}-\rho^{(j)}|$ the number of mistakes of WMR. Suppose the weak independence condition holds. Then, for every trial $j = 1,\dots,t$,
--   $$
--   \mathbf E\big(|\lambda^{(j)}-\rho^{(j)}| \,\big|\, (x^{(1)},\rho^{(1)}),\dots,(x^{(j)},\rho^{(j)})\big) = |\gamma^{(j)}-\rho^{(j)}| \quad\text{almost surely},
--   $$
--   and consequently
--   $$
--   \mathbf E(m) = \mathbf E\Big(\sum_{j=1}^t |\lambda^{(j)}-\rho^{(j)}|\Big) = \mathbf E\Big(\sum_{j=1}^t |\gamma^{(j)}-\rho^{(j)}|\Big).
--   $$
--
--   This identity reduces the expected number of mistakes of the randomized algorithm to the total absolute loss of the deterministic weighted-average master WMC on the same weights, so that the pathwise loss bound for WMC applies.
--
--   **Formalization Note** Both expectations are Bochner integrals of bounded measurable functions (each summand lies in $[0,1]$), so no integrability hypothesis is needed. Trials are indexed from $0$ to $t-1$ in Lean.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 240, Section 6, proof of Theorem 6.1

import Mathlib
import Definitions.Def_WeightedMajority_Randomized_WMRModel

open MeasureTheory

namespace WeightedMajority.Randomized

/-- §6, p. 240, proof of Theorem 6.1: under the weak independence condition the conditional
expected mistake indicator of each trial is `|γ^{(j)} − ρ^{(j)}|`, and the expected number of
mistakes of WMR equals the expected total loss `E(Σ_j |γ^{(j)} − ρ^{(j)}|)`. -/
theorem expected_mistakes_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam) :
    (∀ j < t, P[fun ω => |lam j ω - ρ j ω| | history x ρ j]
        =ᵐ[P] fun ω => |gamma w1 F x ρ j ω - ρ j ω|) ∧
    ∫ ω, mistakes t lam ρ ω ∂P
      = ∫ ω, ∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω| ∂P := by sorry

end WeightedMajority.Randomized
