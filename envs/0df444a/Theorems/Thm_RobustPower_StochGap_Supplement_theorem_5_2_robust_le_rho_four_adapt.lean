-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_5_2_robust_le_rho_four_adapt
-- name    : RobustPower.StochGap.Supplement.theorem_5_2_robust_le_rho_four_adapt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:36:05.664515+00:00
-- url     : https://prove2.me/theorems/bc5e6024-2a2b-40a6-8ddd-d0007ab8bc57
-- title:
--   Theorem 5.2, p. 29 — improved adaptability gap 4/(1+ρ) under symmetric right-hand-side and cost uncertainty
-- statement:
--   Consider the robust problem $\Pi_{\mathrm{Rob}}(b,d)$ (1.5) and the fully adaptive problem $\Pi_{\mathrm{Adapt}}(b,d)$ (1.6), in which both the right-hand side $b(\omega)\in\mathbb R^m_+$ and the second-stage cost $d(\omega)\in\mathbb R^{n_2}_+$ depend on the scenario $\omega\in\Omega$. Data: $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}_+$; both stages may have integer coordinates. The uncertainty set is $I_{(b,d)}(\Omega)=\{(b(\omega),d(\omega)):\omega\in\Omega\}\subseteq\mathbb R^{m+n_2}_+$. $z_{\mathrm{Rob}}(b,d)$ is the least worst-case cost $c^Tx+\max_\omega d(\omega)^Ty$ of one pair $(x,y)$ with $Ax+By\ge b(\omega)$ for all $\omega$, and $z_{\mathrm{Adapt}}(b,d)$ the least worst-case cost $c^Tx+\max_\omega d(\omega)^Ty(\omega)$ of a first-stage $x$ and a recourse $y(\omega)$ with $Ax+By(\omega)\ge b(\omega)$ for all $\omega$.
--
--   Suppose $I_{(b,d)}(\Omega)$ is symmetric (Definition 1.2). Let
--   $$b^l_j=\min\{b_j : (b,d)\in I_{(b,d)}(\Omega)\},\quad b^h_j=\max\{b_j : (b,d)\in I_{(b,d)}(\Omega)\}\quad(j=1,\dots,m),$$
--   $$d^l_j=\min\{d_j : (b,d)\in I_{(b,d)}(\Omega)\},\quad d^h_j=\max\{d_j : (b,d)\in I_{(b,d)}(\Omega)\}\quad(j=1,\dots,n_2),$$
--   and suppose $b^l\ge\rho\,b^h$ and $d^l\ge\rho\,d^h$ for some $\rho\ge0$. Then
--   $$z_{\mathrm{Rob}}(b,d)\ \le\ \frac{4}{1+\rho}\, z_{\mathrm{Adapt}}(b,d).$$
--
--   For $\rho=0$ this is Theorem 5.1; uncertainty sets bounded away from zero give a smaller gap.
--
--   **Formalization Note** The extrema are attained coordinate values (IsLeast / IsGreatest of $\{b_j(\omega)\}$, $\{d_j(\omega)\}$), without assuming the set is closed. Integer coordinates are allowed in both stages. Values are the published `AdaptGap.zRob`, `AdaptGap.zAdapt` (EReal infima).
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - encoding: x ∈ ℝ^{n₁−p₁}₊ × ℤ^{p₁}₊, y ∈ ℝ^{n₂−p₂}₊ × ℤ^{p₂}₊ → nonnegative vectors integer on coordinate sets I₁ ⊆ Fin n₁, I₂ ⊆ Fin n₂; reason: the same domains up to relabelling coordinates; published convention of the base mission
--   - encoding: bˡ, bʰ, dˡ, dʰ defined by min and max over I_(b,d)(Ω) → least and greatest elements of the coordinate values over Ω (IsLeast / IsGreatest); reason: this is what min and max mean; the set is not assumed closed
--   - reading: (1.5)–(1.6) print the integer factor as ℤ₊^{n₂} next to ℝ₊^{n₂−p₂} → the published mixedIntDomain I₂ has n₂ coordinates, p₂ of them integer; reason: the printed factors have inconsistent total dimension unless p₂=n₂; §5 explicitly describes the same mixed-integer model, and (1.2)–(1.3) give its correctly dimensioned ℤ₊^{p₂} factor. This is the inherited model notation repair; no source instance is excluded.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 29, Theorem 5.2 and its proof (pp. 29–30)

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 5.2 (p. 29): if the paired uncertainty set `I_{(b,d)}(Ω) ⊆ ℝ^{m+n₂}₊` is symmetric,
`bˡ, bʰ, dˡ, dʰ` are its attained coordinatewise minima and maxima, and `bˡ ≥ ρ • bʰ`,
`dˡ ≥ ρ • dʰ` for some `ρ ≥ 0`, then `z_Rob(b, d) ≤ (4 / (1 + ρ)) · z_Adapt(b, d)`, with
integer coordinates `I₁`, `I₂` allowed in both stages. -/
theorem theorem_5_2_robust_le_rho_four_adapt {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hsym : RobustPower.StochGap.IsSymmetric (RobustPower.AdaptGap.scenarioSet b d))
    (bl bh : Fin m → ℝ) (dl dh : Fin n₂ → ℝ)
    (hbl : ∀ j, IsLeast (Set.range fun ω => b ω j) (bl j))
    (hbh : ∀ j, IsGreatest (Set.range fun ω => b ω j) (bh j))
    (hdl : ∀ j, IsLeast (Set.range fun ω => d ω j) (dl j))
    (hdh : ∀ j, IsGreatest (Set.range fun ω => d ω j) (dh j))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρb : ρ • bh ≤ bl) (hρd : ρ • dh ≤ dl) :
    RobustPower.AdaptGap.zRob A B b c d I₁ I₂ ≤
      ((4 / (1 + ρ) : ℝ) : EReal) * RobustPower.AdaptGap.zAdapt A B b c d I₁ I₂ := by sorry

end RobustPower.StochGap.Supplement
