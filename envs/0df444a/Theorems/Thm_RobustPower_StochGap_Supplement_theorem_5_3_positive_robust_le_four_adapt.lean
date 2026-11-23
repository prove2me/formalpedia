-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_5_3_positive_robust_le_four_adapt
-- name    : RobustPower.StochGap.Supplement.theorem_5_3_positive_robust_le_four_adapt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:36:36.176985+00:00
-- url     : https://prove2.me/theorems/3587d3e6-8ca2-43cf-a526-a819b04d57bf
-- title:
--   Theorem 5.3, p. 30 — the adaptability gap is at most 4 for convex positive right-hand-side and cost uncertainty
-- statement:
--   Consider the robust problem $\Pi_{\mathrm{Rob}}(b,d)$ (1.5) and the fully adaptive problem $\Pi_{\mathrm{Adapt}}(b,d)$ (1.6), in which both the right-hand side $b(\omega)\in\mathbb R^m_+$ and the second-stage cost $d(\omega)\in\mathbb R^{n_2}_+$ depend on the scenario $\omega\in\Omega$. Data: $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}_+$; both stages may have integer coordinates. The uncertainty set is $I_{(b,d)}(\Omega)=\{(b(\omega),d(\omega)):\omega\in\Omega\}\subseteq\mathbb R^{m+n_2}_+$. $z_{\mathrm{Rob}}(b,d)$ is the least worst-case cost $c^Tx+\max_\omega d(\omega)^Ty$ of one pair $(x,y)$ with $Ax+By\ge b(\omega)$ for all $\omega$, and $z_{\mathrm{Adapt}}(b,d)$ the least worst-case cost $c^Tx+\max_\omega d(\omega)^Ty(\omega)$ of a first-stage $x$ and a recourse $y(\omega)$ with $Ax+By(\omega)\ge b(\omega)$ for all $\omega$.
--
--   Suppose the uncertainty set $I_{(b,d)}(\Omega)\subseteq\mathbb R^{m+n_2}$ is convex and positive (Definition 1.3). Then
--   $$z_{\mathrm{Rob}}(b,d)\ \le\ 4\, z_{\mathrm{Adapt}}(b,d).$$
--
--   This extends Theorem 5.1 from symmetric to positive uncertainty sets.
--
--   **Formalization Note** A pair $(b,d)$ is identified with the vector of $\mathbb R^{m+n_2}$ obtained by concatenating $b$ and $d$ (`Fin.append`), a linear isomorphism, and positivity is the published `IsPositive` of the image of $\omega\mapsto(b(\omega),d(\omega))$. Values are the published `AdaptGap.zRob`, `AdaptGap.zAdapt`.
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - encoding: x ∈ ℝ^{n₁−p₁}₊ × ℤ^{p₁}₊, y ∈ ℝ^{n₂−p₂}₊ × ℤ^{p₂}₊ → nonnegative vectors integer on coordinate sets I₁ ⊆ Fin n₁, I₂ ⊆ Fin n₂; reason: the same domains up to relabelling coordinates; published convention of the base mission
--   - encoding: I_(b,d)(Ω) ⊆ ℝ^{m+n₂} → the range of ω ↦ Fin.append (b ω) (d ω) in Fin (m + n₂) → ℝ; reason: concatenation is the coordinate identification ℝ^m × ℝ^{n₂} = ℝ^{m+n₂}; it preserves convexity, symmetry and nonnegativity
--   - reading: (1.5)–(1.6) print the integer factor as ℤ₊^{n₂} next to ℝ₊^{n₂−p₂} → the published mixedIntDomain I₂ has n₂ coordinates, p₂ of them integer; reason: the printed factors have inconsistent total dimension unless p₂=n₂; §5 explicitly describes the same mixed-integer model, and (1.2)–(1.3) give its correctly dimensioned ℤ₊^{p₂} factor. This is the inherited model notation repair; no source instance is excluded.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 30, Theorem 5.3 and its proof; Definition 1.3, p. 6

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 5.3 (p. 30): if the paired uncertainty set `I_{(b,d)}(Ω)`, viewed in `ℝ^{m+n₂}` by
concatenating `b(ω)` and `d(ω)`, is convex and positive (Definition 1.3), then
`z_Rob(b, d) ≤ 4 · z_Adapt(b, d)`, with integer coordinates `I₁`, `I₂` allowed in both
stages. -/
theorem theorem_5_3_positive_robust_le_four_adapt {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hpos : RobustPower.StochGap.IsPositive (Set.range fun ω => Fin.append (b ω) (d ω))) :
    RobustPower.AdaptGap.zRob A B b c d I₁ I₂ ≤
      4 * RobustPower.AdaptGap.zAdapt A B b c d I₁ I₂ := by sorry

end RobustPower.StochGap.Supplement
