-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_4_7
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_4_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:36:28.481094+00:00
-- url     : https://prove2.me/theorems/86de0467-56e8-4be6-b349-5aaff396fdc2
-- title:
--   Corollary 4.7
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   For any finite positive pairs $(A_i,B_i)$ and weights $p_i\ge0$, and operator convex $f$,
--
--   $$S_f\!\left(\sum_i p_iA_i\middle\Vert\sum_i p_iB_i\right)\le\sum_i p_iS_f(A_i\Vert B_i).$$
--
--   The weights need not sum to one. Empty sums and zero weights use the source's $0\cdot\infty=0$ convention. This is joint convexity together with homogeneity.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 20, Corollary 4.7

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

/-- Corollary 4.7, PDF p.20: arbitrary finite nonnegative weights, including all-zero weights. -/
theorem corollary_4_7 [Nonempty I] {r : ℕ} (X Y : Fin r → Mat I)
    (hX : ∀ i, (X i).PosSemidef) (hY : ∀ i, (Y i).PosSemidef)
    (p : Fin r → ℝ) (hp : ∀ i, 0 ≤ p i) (f : ℝ → ℝ)
    (hf : DivergenceGenerator f) (hconv : SemidefiniteOperatorConvex f) :
    div f (∑ i, (p i : ℂ) • X i) (∑ i, (p i : ℂ) • Y i) ≤
      ∑ i, (p i : EReal) * div f (X i) (Y i) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
