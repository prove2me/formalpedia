-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_4_5_positive_robust_le_two_adapt
-- name    : RobustPower.StochGap.Supplement.theorem_4_5_positive_robust_le_two_adapt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:35:21.77982+00:00
-- url     : https://prove2.me/theorems/14b144c1-7e13-49ec-b34b-ac8353164a18
-- title:
--   Theorem 4.5, p. 27 — the adaptability gap is at most 2 for convex positive right-hand-side uncertainty
-- statement:
--   Consider the robust problem $\Pi_{\mathrm{Rob}}(b)$ (1.2) and the fully adaptive problem $\Pi_{\mathrm{Adapt}}(b)$ (1.3): data $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, costs $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, scenarios $\omega\in\Omega$ with right-hand sides $b(\omega)\in\mathbb R^m_+$ and uncertainty set $I_b(\Omega)=\{b(\omega):\omega\in\Omega\}$. Both stages may have integer coordinates: $x\in\mathbb R^{n_1-p_1}_+\times\mathbb Z^{p_1}_+$ and $y\in\mathbb R^{n_2-p_2}_+\times\mathbb Z^{p_2}_+$. $z_{\mathrm{Rob}}(b)$ is the least cost $c^Tx+d^Ty$ of one pair $(x,y)$ with $Ax+By\ge b(\omega)$ for all $\omega$; $z_{\mathrm{Adapt}}(b)$ is the least worst-case cost $c^Tx+\max_\omega d^Ty(\omega)$ of a first-stage $x$ and a recourse $y(\omega)$ chosen after $\omega$ is revealed, with $Ax+By(\omega)\ge b(\omega)$ for all $\omega$.
--
--   Suppose the uncertainty set $I_b(\Omega)$ is convex and positive (Definition 1.3): there is a convex symmetric set $S\subseteq\mathbb R^m_+$ with $I_b(\Omega)\subseteq S$ whose point of symmetry lies in $I_b(\Omega)$. Then
--   $$z_{\mathrm{Rob}}(b)\ \le\ 2\, z_{\mathrm{Adapt}}(b).$$
--
--   This extends Theorem 4.1 from symmetric to positive uncertainty sets, such as translates of the simplex away from the origin.
--
--   **Formalization Note** Positivity is the published `IsPositive`, which bundles convexity of $I_b(\Omega)$, nonnegativity, and the enclosing convex symmetric nonnegative set $S$ with its centre in $I_b(\Omega)$. The adaptive value is `AdaptGap.zAdapt` with the constant cost $d(\omega)=d$.
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - encoding: x ∈ ℝ^{n₁−p₁}₊ × ℤ^{p₁}₊, y ∈ ℝ^{n₂−p₂}₊ × ℤ^{p₂}₊ → nonnegative vectors integer on coordinate sets I₁ ⊆ Fin n₁, I₂ ⊆ Fin n₂; reason: the same domains up to relabelling coordinates; published convention of the base mission
--   - encoding: z_Adapt(b) of (1.3) and z_Rob(b) of (1.2) → AdaptGap.zAdapt with the constant cost d(ω) = d, and StochGap.zRob, where max_ω dᵀy is written dᵀy; reason: the two agree because the uncertainty set here is nonempty, so the maximum of a constant is that constant
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 27, Theorem 4.5 and its proof; Definition 1.3, p. 6

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 4.5 (p. 27): if the right-hand-side uncertainty set `range b` is convex and positive
(Definition 1.3), then `z_Rob(b) ≤ 2 · z_Adapt(b)`, with integer coordinates `I₁`, `I₂`
allowed in both stages. -/
theorem theorem_4_5_positive_robust_le_two_adapt {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (hpos : RobustPower.StochGap.IsPositive (Set.range b)) :
    RobustPower.StochGap.zRob A B b I₁ I₂ c d ≤
      2 * RobustPower.AdaptGap.zAdapt A B b c (fun _ => d) I₁ I₂ := by sorry

end RobustPower.StochGap.Supplement
