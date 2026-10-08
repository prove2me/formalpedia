-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_gamma_measurable
-- name    : StochConvexProg.FirstStage.gamma_measurable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:04.229722+00:00
-- url     : https://prove2.me/theorems/65a93b8e-bc9b-4bd6-a13b-a03b966c1a40
-- title:
--   Proof of Theorem 1, p. 187 — Γ (3.10) is a measurable multifunction, ρ is measurable, nearest-point selection
-- statement:
--   Fix $x_1\in\mathbb R^{n_1}$ and let $\Gamma(s)=\{x_2\in\mathbb R^{n_2}\mid x_2\in C_2,\ f_{2i}(s,x_1,x_2)\le 0,\ i=1,\dots,m_2\}$ be the set of feasible recourses (3.10). Then:
--
--   1. $\Gamma$ is a measurable multifunction: $\{s\in S\mid \Gamma(s)\cap K\ne\emptyset\}$ is measurable for every closed $K\subseteq\mathbb R^{n_2}$;
--   2. $s\mapsto\rho(s,x_1)=\operatorname{dist}(0,\Gamma(s))$ is measurable;
--   3. there is a measurable $x_2:S\to\mathbb R^{n_2}$ such that, for every $s$ with $\Gamma(s)\ne\emptyset$, $x_2(s)\in\Gamma(s)$ and $|x_2(s)|=\rho(s,x_1)$, i.e. $x_2(s)$ is the point of $\Gamma(s)$ nearest the origin.
--
--   This is the step of the proof of Theorem 1 that produces an essentially bounded feasible recourse from the hypothesis on $\rho$.
--
--   **Formalization Note** Measurability of a multifunction is the published definition `DupacovaWets.Consistency.IsMeasurableMultifunction`. $|\cdot|$ is the Euclidean length. The set $\{s\mid\Gamma(s)\ne\emptyset\}$ is the paper's $S'$ (3.3); a measurable function on $S'$ is stated as a measurable function on $S$ whose values on $S'$ have the required property.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 187, proof of Theorem 1, paragraph after (3.10)

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_FirstStage
import Definitions.Def_DupacovaWets_Consistency_Multifunction

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Proof of Theorem 1, p. 187: for each `x₁`, the feasible-recourse multifunction `Γ` of (3.10) is
measurable, `ρ(s, x₁) = dist(0, Γ(s))` is measurable in `s`, and there is a measurable `x₂` with
`x₂(s)` a point of `Γ(s)` nearest `0` whenever `Γ(s) ≠ ∅` (i.e. `s ∈ S′`). -/
theorem gamma_measurable {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (x₁ : Fin n₁ → ℝ) :
    DupacovaWets.Consistency.IsMeasurableMultifunction (fun s => pr.Γ x₁ s) ∧
      Measurable (fun s => pr.ρ s x₁) ∧
      ∃ x₂ : S → (Fin n₂ → ℝ), Measurable x₂ ∧
        ∀ s, (pr.Γ x₁ s).Nonempty →
          x₂ s ∈ pr.Γ x₁ s ∧ ((eucNorm (x₂ s) : ℝ) : EReal) = pr.ρ s x₁ := by sorry

end StochConvexProg.FirstStage
