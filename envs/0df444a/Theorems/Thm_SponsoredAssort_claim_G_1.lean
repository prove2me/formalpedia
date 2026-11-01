-- Prove2me | Theorems.Thm_SponsoredAssort_claim_G_1
-- name    : SponsoredAssort.claim_G_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:07.545675+00:00
-- url     : https://prove2.me/theorems/4c2a5de1-035b-4f8b-a38b-246231ada3b2
-- title:
--   Claim G.1 — $\delta$ is unimodal with maximum at $\sqrt{a(S_1)a(S_2)}$ and symmetric under $y\mapsto a(S_1)a(S_2)/y$
-- statement:
--   Fix a seller $i$ with $r_i>0$ and the others' attractiveness $v_{-i}$, and write $a(S)=1+\sum_{j\in S\setminus\{i\}}v_j$. Let $S_1,S_2$ be assortments with $i\in S_1$, $i\in S_2$ and $a(S_1)<a(S_2)$, and define $\delta:\mathbb R_+\to\mathbb R$ by
--
--   $$
--   \delta(y)=r_i\,\pi_i\big(S_1,(y,v_{-i})\big)-r_i\,\pi_i\big(S_2,(y,v_{-i})\big).
--   $$
--
--   Then $\delta$ is unimodal with its maximum at $c=\sqrt{a(S_1)a(S_2)}$:
--
--   1. $\delta$ is strictly increasing on $[0,c]$;
--   2. $\delta$ is strictly decreasing on $[c,\infty)$;
--   3. $\delta(y)=\delta\big(a(S_1)a(S_2)/y\big)$ for every $y>0$.
--
--   The claim compares two assortments containing seller $i$ as seller $i$'s attractiveness varies, and drives Corollary 5.1.
--
--   Differences from the source:
--   - encoding: unimodal (increasing and then decreasing) with a maximum at $\sqrt{a(S_1)a(S_2)}$ → strictly increasing on $[0,c]$ and strictly decreasing on $[c,\infty)$; reason: this is the meaning of unimodality with maximum at $c$
--   - encoding: $\delta(y)=\delta(a(S_1)a(S_2)/y)$ for all $y$ → for all $y>0$; reason: $a(S_1)a(S_2)/y$ is undefined at $y=0$
--   - generalization: standing revenues $r_1\ge\dots\ge r_n>0$ → only $r_i>0$; reason: the claim involves only $r_i$; it specializes to the standing setting
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Appendix G.1, Claim G.1, OA p.36

import Mathlib
import Definitions.Def_SponsoredAssort_choiceProb
import Definitions.Def_SponsoredAssort_others

open scoped NNReal

namespace SponsoredAssort

/-- **Claim G.1** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), Appendix G.1, OA p.36). Fix a
seller `i` with `rᵢ > 0` and `v₋ᵢ`, and write `a(S) = 1 + ∑_{j ∈ S \ {i}} vⱼ`. For assortments
`S₁, S₂` with `i ∈ S₁`, `i ∈ S₂` and `a(S₁) < a(S₂)`, the function
`δ(y) = rᵢ · πᵢ(S₁, (y, v₋ᵢ)) − rᵢ · πᵢ(S₂, (y, v₋ᵢ))` on `ℝ₊` is unimodal with maximum at
`√(a(S₁)a(S₂))`: strictly increasing on `[0, √(a(S₁)a(S₂))]` and strictly decreasing on
`[√(a(S₁)a(S₂)), ∞)`. Moreover `δ(y) = δ(a(S₁)a(S₂)/y)`.

**Formalization Note.** "Unimodal (increasing and then decreasing) with a maximum at `√(a₁a₂)`" is
stated as strict monotonicity on each side of `√(a₁a₂)`. The symmetry is stated for `y > 0`,
where `a₁a₂/y` is defined; `a₁a₂/y ≥ 0`, so `Real.toNNReal` is exact. `rᵢ > 0` is the paper's
standing assumption (p.9). -/
theorem claim_G_1 {n : ℕ} (r : Fin n → ℝ) (v : Attr n) (i : Fin n) (hr : 0 < r i)
    (S₁ S₂ : Finset (Fin n)) (h₁ : i ∈ S₁) (h₂ : i ∈ S₂) (ha : others v i S₁ < others v i S₂) :
    let δ : ℝ≥0 → ℝ := fun y =>
      r i * choiceProb S₁ (Function.update v i y) i - r i * choiceProb S₂ (Function.update v i y) i
    (∀ y z : ℝ≥0, y < z → (z : ℝ) ≤ Real.sqrt (others v i S₁ * others v i S₂) → δ y < δ z) ∧
    (∀ y z : ℝ≥0, Real.sqrt (others v i S₁ * others v i S₂) ≤ (y : ℝ) → y < z → δ z < δ y) ∧
    (∀ y : ℝ≥0, 0 < y →
      δ y = δ (Real.toNNReal (others v i S₁ * others v i S₂ / (y : ℝ)))) := by sorry

end SponsoredAssort
