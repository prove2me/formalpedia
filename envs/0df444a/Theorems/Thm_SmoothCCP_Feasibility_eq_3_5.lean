-- Prove2me | Theorems.Thm_SmoothCCP_Feasibility_eq_3_5
-- name    : SmoothCCP.Feasibility.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:26.186975+00:00
-- url     : https://prove2.me/theorems/8cf4c43e-d390-4e7b-9334-996a702f6f79
-- title:
--   (3.5), p. 14 — Theorem 3.11 on the net Z: ℙ(Z^{N,t}_{δ−β} ⊆ Z_{α−β}) ≥ 1 − ⌈1/β⌉⌈2LD/t⌉ⁿ exp{−2NM²}
-- statement:
--   Work in the setting of Theorem 3.8 (closed $X$, $\alpha\in(0,1)$, admissible $\gamma_\varepsilon$, an i.i.d. sample of size $N\ge1$, Assumption 3.1), and suppose Assumption 3.7 holds with $t>0$ and $\delta\in(0,\alpha]$, with $M=\inf_{x\in X}M_x>0$. Let $L,D>0$, $\beta\in(0,\delta]$, and let $Z\subseteq X$ be a finite set with
--   $$|Z|\le\lceil1/\beta\rceil\,\lceil 2LD/t\rceil^n .$$
--   Define
--   $$Z_{\alpha-\beta}=\{x\in Z\mid F(0;x)\ge 1-\alpha+\beta\},\qquad Z^{N,t}_{\delta-\beta}=\{x\in Z\mid F^N_\varepsilon(-t;x)\ge1-\delta+\beta\}.$$
--   Then
--   $$\mathbb P\bigl(Z^{N,t}_{\delta-\beta}\subseteq Z_{\alpha-\beta}\bigr)\ge 1-\lceil1/\beta\rceil\lceil 2LD/t\rceil^n\exp\{-2NM^2\}.$$
--
--   This is Theorem 3.11 applied to the finite net $Z$ with the risk levels $\alpha$ and $\delta$ both lowered by $\beta$; the margin $M_x$ is unchanged by that shift.
--
--   **Formalization Note** The conclusion is in the complement form with outer measure, as in Theorem 3.11. In the paper $Z=\bigcup_j Z_j$ is the net of the previous step; here $Z$ is any finite subset of $X$ obeying the cardinality bound, which is what the step uses. The case $\beta=\delta=\alpha$ (level $\alpha-\beta=0$) is allowed, as on the page.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Theorem 3.13, (3.5), p. 14

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
open MeasureTheory

namespace SmoothCCP.Feasibility

theorem eq_3_5 {n N : ℕ} {Ξ Ω : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Fin N → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = Pξ) (hN : 1 ≤ N)
    (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (hC : ∀ x ∈ X, Measurable (C x)) (hcont : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (α ε : ℝ) (γ : ℝ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγ : AdmissibleGamma ε γ)
    (D L : ℝ) (hD : 0 < D) (hL : 0 < L)
    (t δ M : ℝ) (ht : 0 < t) (hδ0 : 0 < δ) (hδα : δ ≤ α) (hM : 0 < M)
    (hMx : ∀ x ∈ X, M ≤ margin Pξ C ε γ t α δ x)
    (β : ℝ) (hβ0 : 0 < β) (hβδ : β ≤ δ)
    (Z : Finset (Fin n → ℝ)) (hZX : (↑Z : Set (Fin n → ℝ)) ⊆ X)
    (hZcard : (Z.card : ℝ) ≤ (⌈1 / β⌉₊ : ℝ) * (⌈2 * L * D / t⌉₊ : ℝ) ^ n) :
    P {ω | ¬ {x | x ∈ Z ∧ 1 - δ + β ≤ sampleCdf C ε γ (fun i => ξ i ω) (-t) x} ⊆
          {x | x ∈ Z ∧ 1 - α + β ≤ cdf Pξ C 0 x}}
      ≤ ENNReal.ofReal
          ((⌈1 / β⌉₊ : ℝ) * (⌈2 * L * D / t⌉₊ : ℝ) ^ n * Real.exp (-2 * (N : ℝ) * M ^ 2)) := by sorry

end SmoothCCP.Feasibility
