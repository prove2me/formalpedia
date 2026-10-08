-- Prove2me | Theorems.Thm_RobustPower_StochGap_theorem_2_1_robust_le_two_stoch
-- name    : RobustPower.StochGap.theorem_2_1_robust_le_two_stoch
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:15:18.81685+00:00
-- url     : https://prove2.me/theorems/bdd1c91a-2433-4ff3-8284-ef3c51802b9d
-- title:
--   Theorem 2.1 — for symmetric right-hand-side uncertainty, $z_{\mathrm{Rob}}(b)\le 2\, z_{\mathrm{Stoch}}(b)$
-- statement:
--   Consider the two-stage stochastic problem $\Pi_{\mathrm{Stoch}}(b)$ and the two-stage robust problem $\Pi_{\mathrm{Rob}}(b)$ of (1.1)–(1.2), with $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, right-hand sides $b(\omega)\in\mathbb R^m_+$ for every scenario $\omega$ of a set $\Omega$ carrying a probability measure $\mu$, arbitrary integer first-stage coordinates $I_1$, and no integer second-stage variables ($p_2=0$). Assume:
--   1. the uncertainty set $I_b(\Omega)=\{b(\omega):\omega\in\Omega\}$ is symmetric, with point of symmetry $b(\omega^0)$;
--   2. $b$ is $\mu$-integrable and condition (2.1) holds: $\mathbb E_\mu[b(\omega)]\ge b(\omega^0)$.
--
--   Then
--   $$z_{\mathrm{Rob}}(b)\ \le\ 2\cdot z_{\mathrm{Stoch}}(b).$$
--
--   A single static solution, computable without knowing $\mu$, therefore costs in the worst case at most twice the optimal expected cost of a fully adaptive policy. By Lemma 2.1, (2.1) holds for every symmetric probability measure.
--
--   **Formalization Note** Both optimal values are extended-real infima ($+\infty$ if infeasible) and no optimal solution is assumed to exist. Second-stage policies are integrable and constraints hold for every scenario. Integrability of $b$ makes (2.1) meaningful.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 10, Theorem 2.1 (proof pp. 13–14)

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems

open MeasureTheory Matrix

namespace RobustPower.StochGap

/-- Theorem 2.1 (p. 10): with no integer second-stage variables (`p₂ = 0`, i.e. `I₂ = ∅`), a
symmetric uncertainty set `I_b(Ω) = range b ⊆ ℝᵐ₊` with point of symmetry `b(ω⁰)`, and a
probability measure `μ` with `E_μ[b(ω)] ≥ b(ω⁰)` (2.1), the stochasticity gap is at most two:
`z_Rob(b) ≤ 2 · z_Stoch(b)`. -/
theorem theorem_2_1_robust_le_two_stoch {m n₁ n₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω) (hbint : Integrable b μ)
    (I₁ : Set (Fin n₁)) (ω₀ : Ω)
    (hsym : IsSymmetricAbout (Set.range b) (b ω₀))
    (hmean : b ω₀ ≤ ∫ ω, b ω ∂μ) :
    zRob A B b I₁ ∅ c d ≤ 2 * zStoch μ A B b I₁ ∅ c d := by sorry

end RobustPower.StochGap
