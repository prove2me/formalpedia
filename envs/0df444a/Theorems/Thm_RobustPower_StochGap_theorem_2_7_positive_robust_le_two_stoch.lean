-- Prove2me | Theorems.Thm_RobustPower_StochGap_theorem_2_7_positive_robust_le_two_stoch
-- name    : RobustPower.StochGap.theorem_2_7_positive_robust_le_two_stoch
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:15:20.955993+00:00
-- url     : https://prove2.me/theorems/66c3f530-7d00-43f6-bf04-c1b0a79b9b8e
-- title:
--   Theorem 2.7 — the stochasticity gap is at most 2 for convex positive uncertainty sets
-- statement:
--   Consider $\Pi_{\mathrm{Rob}}(b)$ and $\Pi_{\mathrm{Stoch}}(b)$ with data $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, right-hand sides $b(\omega)\in\mathbb R^m_+$, a probability measure $\mu$ under which $b$ is integrable, integer coordinates $I_1$ in the first stage and none in the second ($p_2=0$). Suppose the uncertainty set $I_b(\Omega)$ is convex and positive (Definition 1.3), and let $T\subseteq\mathbb R^m_+$ be a symmetric set containing $I_b(\Omega)$ whose point of symmetry $b^0$ belongs to $I_b(\Omega)$. If $\mathbb E_\mu[b(\omega)]\ge b^0$, then
--   $$z_{\mathrm{Rob}}(b)\ \le\ 2\cdot z_{\mathrm{Stoch}}(b).$$
--
--   This extends Theorem 2.1 to uncertainty sets that are not symmetric themselves but sit inside a symmetric set centred in them, such as a translate of the simplex.
--
--   **Formalization Note** The paper calls the enclosing set $B$; it is `T` here, since $B$ is the recourse matrix. The hypothesis $p_2=0$ is not repeated in the theorem's sentence but is the standing assumption of the paper's stochasticity-gap results, and the proof uses $\mathbb E_\mu[y^*(\omega)]$ as a second-stage decision. Optimal values are extended-real infima; see the `Problems` definition.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 21, Theorem 2.7

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems

open MeasureTheory Matrix

namespace RobustPower.StochGap

/-- Theorem 2.7 (p. 21): with no integer second-stage variables (`p₂ = 0`, the standing
assumption of §2), if the uncertainty set `I_b(Ω) = range b` is convex and positive, `T ⊆ ℝᵐ₊`
is a symmetric set containing `I_b(Ω)` whose point of symmetry `b⁰` lies in `I_b(Ω)`, and
`E_μ[b(ω)] ≥ b⁰`, then `z_Rob(b) ≤ 2 · z_Stoch(b)`. -/
theorem theorem_2_7_positive_robust_le_two_stoch {m n₁ n₂ : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω) (hbint : Integrable b μ)
    (I₁ : Set (Fin n₁))
    (hpos : IsPositive (Set.range b))
    (T : Set (Fin m → ℝ)) (b₀ : Fin m → ℝ) (hT : ∀ t ∈ T, 0 ≤ t)
    (hTsym : IsSymmetricAbout T b₀) (hsub : Set.range b ⊆ T) (hb₀ : b₀ ∈ Set.range b)
    (hmean : b₀ ≤ ∫ ω, b ω ∂μ) :
    zRob A B b I₁ ∅ c d ≤ 2 * zStoch μ A B b I₁ ∅ c d := by sorry

end RobustPower.StochGap
