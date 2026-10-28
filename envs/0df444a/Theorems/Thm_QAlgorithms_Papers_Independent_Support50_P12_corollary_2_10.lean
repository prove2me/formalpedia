-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_2_10
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_2_10
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:14:12.613271+00:00
-- url     : https://prove2.me/theorems/fe81092a-0bf8-400c-986d-70cdb5fd79d4
-- title:
--   Corollary 2.10
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   Let $g$ satisfy the same generator assumptions as $f$. If $S_f(p\Vert q)=S_g(p\Vert q)$ for every pair of probability laws on every finite alphabet, then for every density pair on any finite quantum system,
--
--   $$S_f(\rho\Vert\sigma)=S_g(\rho\Vert\sigma).$$
--
--   Uniformity over all alphabets includes the product spectral alphabet of a quantum pair. Classical values therefore determine the quantum extension within this class.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 7, Corollary 2.10

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

/-- Corollary 2.10, PDF p.7: agreement on ALL finite classical alphabets determines
agreement on all quantum states. -/
theorem corollary_2_10 [Nonempty I] (f g : ℝ → ℝ)
    (hf : DivergenceGenerator f) (hg : DivergenceGenerator g)
    (hc : ∀ (n : ℕ) (p q : Fin n → ℝ), IsDistribution p → IsDistribution q →
      div f (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))) =
      div g (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))))
    (A : Alg I) (rho sigma : Mat I) (hr : AlgebraDensity A rho) (hs : AlgebraDensity A sigma) :
    div f rho sigma = div g rho sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
