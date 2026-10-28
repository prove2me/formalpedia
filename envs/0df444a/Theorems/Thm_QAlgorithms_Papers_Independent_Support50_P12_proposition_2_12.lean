-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_proposition_2_12
-- name    : QAlgorithms.Papers.Independent.Support50.P12.proposition_2_12
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:18:02.258787+00:00
-- url     : https://prove2.me/theorems/dce24232-9862-4209-adc7-596e1d4486f1
-- title:
--   Proposition 2.12
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   Assume $\omega(f)$ is finite. If $B_k\ge0$ and $B_k\to B$, then
--
--   $$S_f(A\Vert B_k)\longrightarrow S_f(A\Vert B).$$
--
--   No continuity at zero of $f$ is required. The finiteness condition concerns either signed infinite slope.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 8, Proposition 2.12

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

/-- Proposition 2.12, PDF pp.8–9: continuity in the second positive input for
finite signed recession slope; continuity at zero of f is not assumed. -/
theorem proposition_2_12 [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (hw : recessionSlope f ≠ ⊤ ∧ recessionSlope f ≠ ⊥) (A B : Mat I) (seq : ℕ → Mat I)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hseq : ∀ n, (seq n).PosSemidef)
    (hlim : Tendsto seq atTop (𝓝 B)) :
    Tendsto (fun n => div f A (seq n)) atTop (𝓝 (div f A B)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
