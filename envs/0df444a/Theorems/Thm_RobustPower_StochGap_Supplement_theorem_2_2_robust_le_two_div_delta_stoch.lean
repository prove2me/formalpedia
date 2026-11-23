-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_2_2_robust_le_two_div_delta_stoch
-- name    : RobustPower.StochGap.Supplement.theorem_2_2_robust_le_two_div_delta_stoch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:31:31.989007+00:00
-- url     : https://prove2.me/theorems/f7ef529d-5960-4295-9c61-76d806170462
-- title:
--   Theorem 2.2 (corrected: zero RHS, continuous first stage or integral scaling) — stochasticity gap at most 2/δ
-- statement:
--   Consider the two-stage stochastic problem $\Pi_{\mathrm{Stoch}}(b)$ (1.1) and the robust problem $\Pi_{\mathrm{Rob}}(b)$ (1.2): data $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, costs $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, scenarios $\omega\in\Omega$ with right-hand sides $b(\omega)\in\mathbb R^m_+$, uncertainty set $I_b(\Omega)=\{b(\omega):\omega\in\Omega\}$ and a probability measure $\mu$ on $\Omega$. The first-stage decision $x$ is nonnegative with integer values on a set of $p_1$ coordinates; there are no integer second-stage variables ($p_2=0$). $z_{\mathrm{Stoch}}(b)$ is the optimal expected cost $c^Tx+\mathbb E_\mu[d^Ty(\omega)]$ over policies with $Ax+By(\omega)\ge b(\omega)$ for every $\omega$, and $z_{\mathrm{Rob}}(b)$ is the optimal cost $c^Tx+d^Ty$ of a single pair $(x,y)$ feasible for every scenario.
--
--   Suppose $I_b(\Omega)$ is symmetric (Definition 1.2) with point of symmetry $b(\omega^0)$, and that for some $\delta>0$ the point $\delta\,b(\omega^0)$ belongs to $I_b(\Omega)$ and
--   $$\mathbb E_\mu[b(\omega)]\ \ge\ \delta\, b(\omega^0)\qquad(2.16).$$
--   Suppose moreover that every right-hand side is zero, that the first stage is continuous ($p_1=0$) or that $2/\delta$ is a natural number. Then
--   $$z_{\mathrm{Rob}}(b)\ \le\ \frac{2}{\delta}\, z_{\mathrm{Stoch}}(b).$$
--
--   This generalizes Theorem 2.1 (the case $\delta=1$) to probability measures whose mean only dominates a scaled copy of the point of symmetry.
--
--   **Formalization Note** Optimal values are infima in $\overline{\mathbb R}$ (EReal), equal to $+\infty$ when a problem is infeasible; no optimal solution is assumed to exist. The integer coordinates of $x$ form a set $I_1$, and $p_1=0$ is $I_1=\emptyset$. Policies and $b$ are $\mu$-integrable, and feasibility holds in every scenario.
--
--   The correction retains zero right-hand sides without restricting the scaling factor; in that case zero decisions attain both optimal values.
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - encoding: x ∈ ℝ^{n₁−p₁}₊ × ℤ^{p₁}₊, y ∈ ℝ^{n₂−p₂}₊ × ℤ^{p₂}₊ → nonnegative vectors integer on coordinate sets I₁ ⊆ Fin n₁, I₂ ⊆ Fin n₂; reason: the same domains up to relabelling coordinates; published convention of the base mission
--   - reading: E_μ[b(ω)] and E_μ[dᵀy(ω)] are written without conditions → b is μ-integrable and Π_Stoch(b) ranges over μ-integrable policies y; reason: the expectations are only defined for integrable functions; the published goal (Theorem 2.1) uses the same convention
--   - correction: integer first-stage coordinates allowed for every δ > 0 → every b(ω) = 0, or I₁ = ∅ or 2/δ is a natural number; reason: the proof (p. 15) scales x* by 2/δ, which keeps integrality only when 2/δ ∈ ℕ, and the printed claim is false otherwise: m = n₁ = n₂ = 1, A = [4/3], B = [1], c = 1/10, d = 1, x integer, Ω = [0, 2] with b(ω) = ω (symmetric about b(ω⁰) = 1), δ = 4/3, μ the point mass at 4/3 (or uniform on [37/30, 43/30]); then z_Stoch = 1/10 (resp. 1/8) at x = 1 while z_Rob = 1/5 at x = 2, above (3/2)·z_Stoch = 3/20 (resp. 3/16). Excluded by this sufficient repair: nonzero RHS instances with integer first-stage coordinates and 2/δ ∉ ℕ All-zero right-hand sides are retained for arbitrary δ, ρ and integer coordinates: zero decisions are feasible, and nonnegative costs force both optimal values to zero. This is a supported sufficient correction, not a claim that integrality of the factor is necessary for every individual instance.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 14–15, Theorem 2.2, (2.16)–(2.25)

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems

open MeasureTheory Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 2.2 (pp. 14–15), corrected: no integer second-stage variables (`I₂ = ∅`), a
symmetric uncertainty set `range b ⊆ ℝᵐ₊` with point of symmetry `b(ω⁰)`, some `δ > 0` with
`δ • b(ω⁰) ∈ range b` and `E_μ[b] ≥ δ • b(ω⁰)` (2.16). Then `z_Rob(b) ≤ (2/δ) · z_Stoch(b)`,
provided all right-hand sides are zero, the first stage is continuous (`I₁ = ∅`), or the scaling factor `2/δ` is a natural
number (so that scaling preserves the integer first-stage coordinates). -/
theorem theorem_2_2_robust_le_two_div_delta_stoch {m n₁ n₂ : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω) (hbint : Integrable b μ)
    (I₁ : Set (Fin n₁)) (ω₀ : Ω)
    (hsym : RobustPower.StochGap.IsSymmetricAbout (Set.range b) (b ω₀))
    (δ : ℝ) (hδ : 0 < δ) (hδmem : δ • b ω₀ ∈ Set.range b)
    (hmean : δ • b ω₀ ≤ ∫ ω, b ω ∂μ)
    (hscale : (∀ ω, b ω = 0) ∨ I₁ = ∅ ∨ ∃ k : ℕ, 2 / δ = (k : ℝ)) :
    RobustPower.StochGap.zRob A B b I₁ ∅ c d ≤
      ((2 / δ : ℝ) : EReal) * RobustPower.StochGap.zStoch μ A B b I₁ ∅ c d := by sorry

end RobustPower.StochGap.Supplement
