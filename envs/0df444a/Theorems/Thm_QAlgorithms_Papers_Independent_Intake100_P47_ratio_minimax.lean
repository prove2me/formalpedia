-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_ratio_minimax
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.ratio_minimax
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:36:34.507788+00:00
-- url     : https://prove2.me/theorems/14b7f63a-2454-4a1b-8f20-667c886e507f
-- title:
--   Proposition 21: Ratio minimax theorem
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. Let $X\subset(0,\infty)$ be nonempty and convex, and let $Y$ be a nonempty compact Hausdorff space. Let $f:X\times Y\to\mathbb R$ be concave in $x$ and lower semicontinuous in $y$. Assume the source's half-convexlike property: for every $y_1,y_2$ there is one $y_3$ such that $f(x,y_3)\le[f(x,y_1)+f(x,y_2)]/2$ for every $x\in X$. Then, with extended extrema,
--   $$\sup_{x\in X}\inf_{y\in Y}\frac{f(x,y)}x=\inf_{y\in Y}\sup_{x\in X}\frac{f(x,y)}x.$$
--   Strict positivity is the interpretation used by the harmonic-mean proof; no boundedness hypothesis is added. This exchanges the ratio optimizations in the exponent arguments.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 22, Proposition 21: Ratio minimax theorem

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.22, Proposition 21, (A.4).
Strict positivity is pinned by the harmonic-mean proof. Decision domains are
nonempty, as in the standing minimax convention. No boundedness is assumed. -/
theorem ratio_minimax {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [Nonempty Y] (X : Set ℝ) (hX : X.Nonempty) (hpos : ∀ x ∈ X, 0 < x)
    (hc : Convex ℝ X) (f : ℝ → Y → ℝ)
    (hconc : ∀ y, ConcaveOn ℝ X (fun x => f x y)) (hhalf : HalfConvexlike X f)
    (hlsc : ∀ x ∈ X, ∀ a : ℝ, IsOpen {y | a < f x y}) :
    (⨆ x : {x : ℝ // x ∈ X}, ⨅ y : Y, ((f x.val y / x.val : ℝ) : EReal)) =
      (⨅ y : Y, ⨆ x : {x : ℝ // x ∈ X}, ((f x.val y / x.val : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
