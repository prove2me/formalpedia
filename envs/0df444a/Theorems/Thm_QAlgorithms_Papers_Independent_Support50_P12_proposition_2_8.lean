-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_proposition_2_8
-- name    : QAlgorithms.Papers.Independent.Support50.P12.proposition_2_8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:15:35.390299+00:00
-- url     : https://prove2.me/theorems/f3f8d407-cac3-49de-b5fa-189f119e6493
-- title:
--   Proposition 2.8
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   If a function $D$ on the positive pairs of a concrete unital algebra is represented by $S_f$, then
--
--   $$f(x)=\frac{D(xI\Vert I)}{\dim H},\qquad x\ge0.$$
--
--   $$D=S_f=S_g\quad\Longrightarrow\quad f(x)=g(x)\quad(x\ge0).$$
--
--   The scalar-identity values are finite even if other divergence values are infinite. Thus the generator is unique on its intended domain.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 7, Proposition 2.8

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

/-- Proposition 2.8, PDF p.7: restriction to scalar identities determines the generator
on [0,infinity); nonzero representation dimension is essential. -/
theorem proposition_2_8 [Nonempty I] (A : Alg I) (D : Mat I → Mat I → EReal)
    (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (hD : ∀ X ∈ A, ∀ Y ∈ A, X.PosSemidef → Y.PosSemidef → D X Y = div f X Y) :
    (∀ x ≥ 0, f x = (D ((x : ℂ) • 1) 1).toReal / Fintype.card I) ∧
    (∀ g : ℝ → ℝ, DivergenceGenerator g →
      (∀ X ∈ A, ∀ Y ∈ A, X.PosSemidef → Y.PosSemidef → D X Y = div g X Y) →
      ∀ x ≥ 0, f x = g x) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
