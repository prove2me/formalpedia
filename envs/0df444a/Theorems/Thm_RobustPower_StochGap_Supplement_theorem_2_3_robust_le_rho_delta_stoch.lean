-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_2_3_robust_le_rho_delta_stoch
-- name    : RobustPower.StochGap.Supplement.theorem_2_3_robust_le_rho_delta_stoch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:31:57.688408+00:00
-- url     : https://prove2.me/theorems/ef2a8518-aa13-4aba-9c29-4e509fbc5b55
-- title:
--   Theorem 2.3 (corrected: zero RHS, continuous first stage or integral scaling) — improved stochasticity gap 2/(δ(1+ρ))
-- statement:
--   Consider the two-stage stochastic problem $\Pi_{\mathrm{Stoch}}(b)$ (1.1) and the robust problem $\Pi_{\mathrm{Rob}}(b)$ (1.2): data $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, costs $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, scenarios $\omega\in\Omega$ with right-hand sides $b(\omega)\in\mathbb R^m_+$, uncertainty set $I_b(\Omega)=\{b(\omega):\omega\in\Omega\}$ and a probability measure $\mu$ on $\Omega$. The first-stage decision $x$ is nonnegative with integer values on a set of $p_1$ coordinates; there are no integer second-stage variables ($p_2=0$). $z_{\mathrm{Stoch}}(b)$ is the optimal expected cost $c^Tx+\mathbb E_\mu[d^Ty(\omega)]$ over policies with $Ax+By(\omega)\ge b(\omega)$ for every $\omega$, and $z_{\mathrm{Rob}}(b)$ is the optimal cost $c^Tx+d^Ty$ of a single pair $(x,y)$ feasible for every scenario.
--
--   Suppose $I_b(\Omega)$ is symmetric with point of symmetry $b(\omega^0)$, that $\delta>0$, $\delta\,b(\omega^0)\in I_b(\Omega)$ and $\mathbb E_\mu[b(\omega)]\ge\delta\,b(\omega^0)$ (2.16). Let $b^l,b^h\in\mathbb R^m_+$ be the coordinatewise minima and maxima (2.26)
--   $$b^l_j=\min_{b\in I_b(\Omega)} b_j,\qquad b^h_j=\max_{b\in I_b(\Omega)} b_j,$$
--   and suppose $b^l\ge\rho\, b^h$ for some $\rho\ge0$. Suppose moreover that every right-hand side is zero, that the first stage is continuous ($p_1=0$) or that $2/(\delta(1+\rho))$ is a natural number. Then
--   $$z_{\mathrm{Rob}}(b)\ \le\ \frac{2}{\delta(1+\rho)}\, z_{\mathrm{Stoch}}(b).$$
--
--   For $\rho=0$ this is Theorem 2.2; a positive $\rho$ (an uncertainty set bounded away from $0$) improves the bound.
--
--   **Formalization Note** Optimal values are EReal infima (with $+\infty$ for infeasibility). The minima and maxima of (2.26) are bound as attained extremes of the coordinate values $\{b_j(\omega)\}$ without assuming the uncertainty set is closed. The integer first-stage coordinates form a set $I_1$; policies and $b$ are $\mu$-integrable.
--
--   The correction retains zero right-hand sides without restricting the scaling factor; in that case zero decisions attain both optimal values.
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - encoding: x ∈ ℝ^{n₁−p₁}₊ × ℤ^{p₁}₊, y ∈ ℝ^{n₂−p₂}₊ × ℤ^{p₂}₊ → nonnegative vectors integer on coordinate sets I₁ ⊆ Fin n₁, I₂ ⊆ Fin n₂; reason: the same domains up to relabelling coordinates; published convention of the base mission
--   - reading: E_μ[b(ω)] and E_μ[dᵀy(ω)] are written without conditions → b is μ-integrable and Π_Stoch(b) ranges over μ-integrable policies y; reason: the expectations are only defined for integrable functions; the published goal (Theorem 2.1) uses the same convention
--   - encoding: bˡⱼ = min_{b∈I_b(Ω)} bⱼ and bʰⱼ = max_{b∈I_b(Ω)} bⱼ (2.26) → bˡⱼ is the least and bʰⱼ the greatest element of {bⱼ(ω) : ω ∈ Ω} (IsLeast / IsGreatest); reason: this is exactly what min and max mean; the set is not assumed closed or compact
--   - correction: integer first-stage coordinates allowed for every δ > 0, ρ ≥ 0 → every b(ω) = 0, or I₁ = ∅ or 2/(δ(1+ρ)) is a natural number; reason: the argument before the theorem (p. 16) scales x* by a factor 2/(δ(1+ρ)), which keeps integrality only when it is a natural number, and the printed claim is false otherwise: one integer x ≥ 0, one continuous y ≥ 0, A = B = [1], c = 1/20, d = 1, b uniform on [9/10, 11/10] (symmetric about 1), δ = 1, ρ = 9/11; then z_Rob = 1/10 (x = 2) and z_Stoch = 3/40 (x = 1), but (11/10)·(3/40) = 33/400 < 1/10. Excluded by this sufficient repair: nonzero RHS instances with integer first-stage coordinates and 2/(δ(1+ρ)) ∉ ℕ All-zero right-hand sides are retained for arbitrary δ, ρ and integer coordinates: zero decisions are feasible, and nonnegative costs force both optimal values to zero. This is a supported sufficient correction, not a claim that integrality of the factor is necessary for every individual instance.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 16, (2.26) and Theorem 2.3; argument on p. 16 before the theorem

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems

open MeasureTheory Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 2.3 (p. 16), corrected: the hypotheses of Theorem 2.2 together with the attained
coordinatewise extrema `bˡ`, `bʰ` of (2.26) and `bˡ ≥ ρ • bʰ` for some `ρ ≥ 0` give
`z_Rob(b) ≤ (2 / (δ (1 + ρ))) · z_Stoch(b)`, provided all right-hand sides are zero,
the first stage is continuous (`I₁ = ∅`), or the scaling factor `2 / (δ (1 + ρ))` is a natural number. -/
theorem theorem_2_3_robust_le_rho_delta_stoch {m n₁ n₂ : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω) (hbint : Integrable b μ)
    (I₁ : Set (Fin n₁)) (ω₀ : Ω)
    (hsym : RobustPower.StochGap.IsSymmetricAbout (Set.range b) (b ω₀))
    (δ : ℝ) (hδ : 0 < δ) (hδmem : δ • b ω₀ ∈ Set.range b)
    (hmean : δ • b ω₀ ≤ ∫ ω, b ω ∂μ)
    (bl bh : Fin m → ℝ)
    (hbl : ∀ j, IsLeast (Set.range fun ω => b ω j) (bl j))
    (hbh : ∀ j, IsGreatest (Set.range fun ω => b ω j) (bh j))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρb : ρ • bh ≤ bl)
    (hscale : (∀ ω, b ω = 0) ∨ I₁ = ∅ ∨ ∃ k : ℕ, 2 / (δ * (1 + ρ)) = (k : ℝ)) :
    RobustPower.StochGap.zRob A B b I₁ ∅ c d ≤
      ((2 / (δ * (1 + ρ)) : ℝ) : EReal) * RobustPower.StochGap.zStoch μ A B b I₁ ∅ c d := by sorry

end RobustPower.StochGap.Supplement
