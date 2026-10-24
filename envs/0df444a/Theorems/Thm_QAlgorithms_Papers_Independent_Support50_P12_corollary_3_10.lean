-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_3_10
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_3_10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:28:36.553314+00:00
-- url     : https://prove2.me/theorems/6fc4ab8e-0037-400c-864c-ed2c4041ac8f
-- title:
--   Corollary 3.10
-- statement:
--   Let $\gamma:\mathcal A\to\mathcal A$ be a Schwarz contraction on a nonzero concrete finite-dimensional algebra. Let $\alpha$ be a complex-linear functional strictly positive on every nonzero positive element, and assume $\alpha\circ\gamma=\alpha$.
--
--   The fixed set $F=\ker(\mathrm{id}-\gamma)$ is a nonzero finite-dimensional $C^*$-algebra, possibly with its own unit, and $\gamma$ restricts to a $C^*$-morphism on $F$. Moreover,
--
--   $$\|\gamma\|_S=\|\gamma\|=1,\qquad\gamma_\infty(X)=\lim_{n\to\infty}\frac1n\sum_{k=1}^n\gamma^k(X)$$
--
--   exists for every $X\in\mathcal A$ and is an $\alpha$-preserving conditional expectation onto $F$. The draft expands this as a positive linear idempotent fixing $F$, with range $F$ and the $F$-bimodule property. This describes the ergodic fixed algebra.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 14, Corollary 3.10

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Corollary 3.10, PDF pp.14–15: the fixed algebra can have its OWN unit P.
The Cesàro limit is a positive contractive bimodule projection preserving alpha. -/
theorem corollary_3_10 [Nonempty I] (A : Alg I) (g : MatrixMap I I)
    (hc : AlgebraExtension A A g) (hg : SchwarzBound A g 1) (alpha : Mat I →ₗ[ℂ] ℂ)
    (ha : ∀ X ∈ A, X.PosSemidef → X ≠ 0 → 0 < (alpha X).re ∧ (alpha X).im = 0)
    (hinv : ∀ X ∈ A, alpha (g X) = alpha X) :
    let F := {X : Mat I | X ∈ A ∧ g X = X}
    snorm A g = 1 ∧ pnorm g = 1 ∧
    IsClosed F ∧ (0 : Mat I) ∈ F ∧
    (∀ X ∈ F, ∀ Y ∈ F, X + Y ∈ F ∧ X * Y ∈ F) ∧
    (∀ c : ℂ, ∀ X ∈ F, c • X ∈ F) ∧ (∀ X ∈ F, Xᴴ ∈ F) ∧
    (∃ P ∈ F, P ≠ 0 ∧ ∀ X ∈ F, P * X = X ∧ X * P = X) ∧
    (∀ X ∈ F, ∀ Y ∈ F, g (X * Y) = g X * g Y ∧ g (Xᴴ) = (g X)ᴴ) ∧
    ∃ E : MatrixMap I I, AlgebraExtension A A E ∧ PositiveOnConcreteAlgebra A E ∧
      (∀ X ∈ A, Tendsto
        (fun n : ℕ => (((n + 1 : ℕ) : ℂ)⁻¹) • ∑ k ∈ Finset.range (n + 1),
          (g : Mat I → Mat I)^[k + 1] X) atTop (𝓝 (E X))) ∧
      (∀ X ∈ A, E (E X) = E X ∧ alpha (E X) = alpha X ∧ E X ∈ F) ∧
      (∀ X ∈ F, E X = X) ∧
      (∀ X ∈ F, ∀ Y ∈ A, ∀ Z ∈ F, E (X * Y * Z) = X * E Y * Z) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
