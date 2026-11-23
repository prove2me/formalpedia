-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_4_2_robust_le_rho_adapt
-- name    : RobustPower.StochGap.Supplement.theorem_4_2_robust_le_rho_adapt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:33:17.412597+00:00
-- url     : https://prove2.me/theorems/4557f150-8837-48cc-8b8d-81fa91169f0e
-- title:
--   Theorem 4.2 (corrected: zero RHS, continuous stages or integral scaling) — improved adaptability gap 2/(1+ρ)
-- statement:
--   Consider the robust problem $\Pi_{\mathrm{Rob}}(b)$ (1.2) and the fully adaptive problem $\Pi_{\mathrm{Adapt}}(b)$ (1.3): data $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, costs $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, scenarios $\omega\in\Omega$ with right-hand sides $b(\omega)\in\mathbb R^m_+$ and uncertainty set $I_b(\Omega)=\{b(\omega):\omega\in\Omega\}$. Both stages may have integer coordinates: $x\in\mathbb R^{n_1-p_1}_+\times\mathbb Z^{p_1}_+$ and $y\in\mathbb R^{n_2-p_2}_+\times\mathbb Z^{p_2}_+$. $z_{\mathrm{Rob}}(b)$ is the least cost $c^Tx+d^Ty$ of one pair $(x,y)$ with $Ax+By\ge b(\omega)$ for all $\omega$; $z_{\mathrm{Adapt}}(b)$ is the least worst-case cost $c^Tx+\max_\omega d^Ty(\omega)$ of a first-stage $x$ and a recourse $y(\omega)$ chosen after $\omega$ is revealed, with $Ax+By(\omega)\ge b(\omega)$ for all $\omega$.
--
--   Suppose $I_b(\Omega)\subseteq\mathbb R^m_+$ is symmetric, let $b^l,b^h$ be its coordinatewise minima and maxima (2.26), and suppose $b^l\ge\rho\,b^h$ for some $\rho\ge0$. Suppose moreover that every right-hand side is zero, that both stages are continuous ($p_1=p_2=0$) or that $2/(1+\rho)$ is a natural number (that is, $\rho=0$ or $\rho=1$). Then
--   $$z_{\mathrm{Rob}}(b)\ \le\ \frac{2}{1+\rho}\, z_{\mathrm{Adapt}}(b).$$
--
--   For $\rho=0$ this is Theorem 4.1; it is the adaptive counterpart of Theorem 2.3.
--
--   **Formalization Note** Optimal values are EReal infima. The extrema of (2.26) are attained coordinate values, without assuming the set is closed. The adaptive value is `AdaptGap.zAdapt` with the constant cost $d(\omega)=d$.
--
--   The correction retains zero right-hand sides without restricting the scaling factor; in that case zero decisions attain both optimal values.
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - encoding: x ∈ ℝ^{n₁−p₁}₊ × ℤ^{p₁}₊, y ∈ ℝ^{n₂−p₂}₊ × ℤ^{p₂}₊ → nonnegative vectors integer on coordinate sets I₁ ⊆ Fin n₁, I₂ ⊆ Fin n₂; reason: the same domains up to relabelling coordinates; published convention of the base mission
--   - encoding: z_Adapt(b) of (1.3) and z_Rob(b) of (1.2) → AdaptGap.zAdapt with the constant cost d(ω) = d, and StochGap.zRob, where max_ω dᵀy is written dᵀy; reason: the two agree because the uncertainty set here is nonempty, so the maximum of a constant is that constant
--   - encoding: bˡⱼ = min_{b∈I_b(Ω)} bⱼ and bʰⱼ = max_{b∈I_b(Ω)} bⱼ (2.26) → bˡⱼ is the least and bʰⱼ the greatest element of {bⱼ(ω) : ω ∈ Ω} (IsLeast / IsGreatest); reason: this is exactly what min and max mean; the set is not assumed closed or compact
--   - correction: integer coordinates allowed in both stages for every ρ ≥ 0 → every b(ω) = 0, or I₁ = I₂ = ∅, or 2/(1+ρ) is a natural number; reason: the theorem refers to the scaling argument of Theorem 2.3 (no separate proof), which keeps integrality only when 2/(1+ρ) ∈ ℕ, and the printed claim is false otherwise in either stage. Integer second stage: n₁ = 0, B = I₂, d = (1, 1), y integer, b(ω) = (t, 2 − t), t ∈ [9/10, 11/10], ρ = 9/11: z_Rob = 4, z_Adapt = 3, and (11/10)·3 < 4. Integer first stage: one integer x with A = (1, 1)ᵀ, c = 3/20, continuous y, B = I₂, d = (1, 1), same b and ρ: z_Rob = 3/10 (x = 2), z_Adapt = 1/4 (x = 1), and (11/10)·(1/4) = 11/40 < 3/10. Excluded by this sufficient repair: nonzero RHS instances with some integer coordinate and ρ ∉ {0, 1} All-zero right-hand sides are retained for arbitrary δ, ρ and integer coordinates: zero decisions are feasible, and nonnegative costs force both optimal values to zero. This is a supported sufficient correction, not a claim that integrality of the factor is necessary for every individual instance.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 25, Theorem 4.2; p. 16, (2.26) and the argument before Theorem 2.3

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 4.2 (p. 25), corrected: if `range b ⊆ ℝᵐ₊` is symmetric, `bˡ`, `bʰ` are the attained
coordinatewise extrema (2.26) and `bˡ ≥ ρ • bʰ` for some `ρ ≥ 0`, then
`z_Rob(b) ≤ (2 / (1 + ρ)) · z_Adapt(b)`, provided all right-hand sides are zero, both stages are continuous
(`I₁ = I₂ = ∅`) or `2 / (1 + ρ)` is a natural number (`ρ = 0` or `ρ = 1`). -/
theorem theorem_4_2_robust_le_rho_adapt {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (hsym : RobustPower.StochGap.IsSymmetric (Set.range b))
    (bl bh : Fin m → ℝ)
    (hbl : ∀ j, IsLeast (Set.range fun ω => b ω j) (bl j))
    (hbh : ∀ j, IsGreatest (Set.range fun ω => b ω j) (bh j))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρb : ρ • bh ≤ bl)
    (hscale : (∀ ω, b ω = 0) ∨ (I₁ = ∅ ∧ I₂ = ∅) ∨ ∃ k : ℕ, 2 / (1 + ρ) = (k : ℝ)) :
    RobustPower.StochGap.zRob A B b I₁ I₂ c d ≤
      ((2 / (1 + ρ) : ℝ) : EReal) * RobustPower.AdaptGap.zAdapt A B b c (fun _ => d) I₁ I₂ := by sorry

end RobustPower.StochGap.Supplement
