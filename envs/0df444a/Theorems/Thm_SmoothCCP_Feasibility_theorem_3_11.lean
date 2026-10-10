-- Prove2me | Theorems.Thm_SmoothCCP_Feasibility_theorem_3_11
-- name    : SmoothCCP.Feasibility.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:21.255325+00:00
-- url     : https://prove2.me/theorems/67440b1b-58d2-4139-9b47-2564864e5cd9
-- title:
--   Theorem 3.11 — for finite X, ℙ(X^{N,t}_{ε,δ} ⊆ X_α) ≥ 1 − |X \ X_α| exp{−2NM²}
-- statement:
--   Work in the setting of Theorem 3.8: $X\subseteq\mathbb R^n$ closed, $\alpha\in(0,1)$, admissible $\gamma_\varepsilon$, an i.i.d. sample $\xi_1,\dots,\xi_N$ ($N\ge1$) with law $\mathbb P_\xi$, and Assumption 3.1. Suppose that $X$ is finite and that Assumption 3.7 holds with $t\in\mathbb R$, $\delta\in[0,\alpha]$ and $M=\inf_{x\in X}M_x>0$. Then
--   $$\mathbb P\bigl(X^{N,t}_{\varepsilon,\delta}\subseteq X_\alpha\bigr)\ge 1-|X\setminus X_\alpha|\exp\{-2NM^2\}.$$
--
--   For a finite decision set, every point accepted by the shifted sample approximation is feasible for the chance constraint with probability exponentially close to one. Theorem 3.13 reduces the general case to this one through a finite net.
--
--   **Formalization Note** The conclusion is stated in the equivalent complement form $\mathbb P(X^{N,t}_{\varepsilon,\delta}\not\subseteq X_\alpha)\le|X\setminus X_\alpha|\exp\{-2NM^2\}$, with $\mathbb P$ evaluated as an outer measure, so no measurability of the event is assumed; it implies the printed form. $|X\setminus X_\alpha|$ is `Set.ncard`, the cardinality since $X$ is finite. Assumption 3.7 and the standing hypotheses are encoded as in Theorem 3.8.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Theorem 3.11, p. 13

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
open MeasureTheory

namespace SmoothCCP.Feasibility

theorem theorem_3_11 {n N : ℕ} {Ξ Ω : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Fin N → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = Pξ) (hN : 1 ≤ N)
    (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (hC : ∀ x ∈ X, Measurable (C x)) (hcont : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (α ε : ℝ) (γ : ℝ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγ : AdmissibleGamma ε γ)
    (hfin : X.Finite)
    (t δ M : ℝ) (hδ0 : 0 ≤ δ) (hδα : δ ≤ α) (hM : 0 < M)
    (hMx : ∀ x ∈ X, M ≤ margin Pξ C ε γ t α δ x) :
    P {ω | ¬ sampleFeasible C X ε γ (fun i => ξ i ω) t δ ⊆ trueFeasible Pξ C X α}
      ≤ ENNReal.ofReal
          (((X \ trueFeasible Pξ C X α).ncard : ℝ) * Real.exp (-2 * (N : ℝ) * M ^ 2)) := by sorry

end SmoothCCP.Feasibility
