-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_theorem_6_3
-- name    : UPPIntersection.Halfspaces.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:52.300118+00:00
-- url     : https://prove2.me/theorems/fa94e724-82b3-489c-b4df-7d435b12c942
-- title:
--   Theorem 6.3 — sign rank lower bound from measurable continuous arrangements
-- statement:
--   Let $(\mathcal X,P_1)$ and $(\mathcal Y,P_2)$ be probability spaces, let $X\sim P_1$ and $Y\sim P_2$ be independent, and let $E\subseteq\mathcal X\times\mathcal Y$ be measurable. Let $A$ be a sign matrix with finite row set $\mathcal A$ and column set $\mathcal B$, and let $\Pi_1:\mathcal X\to\mathcal A$, $\Pi_2:\mathcal Y\to\mathcal B$ be measurable. Then
--   $$\operatorname{rank}_\pm(A)\ge\frac1{\sup_{f,g}\mathbb E_{X,Y}\bigl[|\langle f(X),g(Y)\rangle|\bigr]},$$
--   where the supremum is over all finite dimensions $r$ and all measurable $f:\mathcal X\to\mathbb R^r$, $g:\mathcal Y\to\mathbb R^r$ with $\|f(x)\|_2,\|g(y)\|_2\le1$ everywhere and
--   $$A_{\Pi_1(x),\Pi_2(y)}\cdot\langle f(x),g(y)\rangle\ge0\quad\text{whenever }(x,y)\notin E .$$
--
--   No smallness of $E$ is assumed here; the band where agreement may fail is specialized in Corollary 6.4.
--
--   Differences from the source:
--   - encoding: sign values in {−1, 1}, with −1 meaning logical true → Bool entries with true standing for +1 (as in the published SignRankMargin sign-rank definition); reason: a relabelling of the two values; the signed AND (−1 iff both are −1) becomes Boolean OR of the stored bits, and sign representation becomes A·R > 0 entrywise
--   - encoding: measurable maps Π₁ : 𝒳 → A, Π₂ : 𝒴 → B into finite sets → every fiber Π₁⁻¹{a}, Π₂⁻¹{b} is measurable; reason: for a finite set with its discrete σ-algebra the two notions coincide
--   - encoding: arbitrary probability spaces → probability measures P₁, P₂ on measurable spaces in Lean's Type; reason: no finiteness or standardness restriction
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 28, Theorem 6.3 (eq. (8)); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_SignMatrices

open MeasureTheory SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces

theorem theorem_6_3 {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (Ebad : Set (Ω₁ × Ω₂)) (hE : MeasurableSet Ebad)
    {X Y : Type} [Fintype X] [Fintype Y] (A : Matrix X Y Bool) (proj₁ : Ω₁ → X) (proj₂ : Ω₂ → Y)
    (hproj₁ : ∀ a, MeasurableSet (proj₁ ⁻¹' {a})) (hproj₂ : ∀ b, MeasurableSet (proj₂ ⁻¹' {b})) :
    1 / sSup {m : ℝ | ∃ (r : ℕ) (f : Ω₁ → EuclideanSpace ℝ (Fin r))
        (g : Ω₂ → EuclideanSpace ℝ (Fin r)),
        Measurable f ∧ Measurable g ∧ (∀ x, ‖f x‖ ≤ 1) ∧ (∀ y, ‖g y‖ ≤ 1) ∧
        (∀ x y, (x, y) ∉ Ebad → 0 ≤ signVal (A (proj₁ x) (proj₂ y)) * inner ℝ (f x) (g y)) ∧
        m = ∫ p : Ω₁ × Ω₂, |inner ℝ (f p.1) (g p.2)| ∂(P₁.prod P₂)} ≤ (signRank A : ℝ) := by sorry

end UPPIntersection.Halfspaces
