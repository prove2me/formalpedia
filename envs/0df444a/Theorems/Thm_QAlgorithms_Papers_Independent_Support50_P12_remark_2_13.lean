-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_remark_2_13
-- name    : QAlgorithms.Papers.Independent.Support50.P12.remark_2_13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:19:16.830402+00:00
-- url     : https://prove2.me/theorems/d3e2ce4b-5269-4891-87a3-6748de5127e9
-- title:
--   Remark 2.13
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   Assume $\dim H\ge2$ and $\omega(f)\in\{-\infty,+\infty\}$. Let $x,x_k$ be unit vectors with $x_k\to x$ and no $x_k$ proportional to $x$. Set $A=|x\rangle\langle x|$, $B_k=|x_k\rangle\langle x_k|$. Then
--
--   $$B_k\to A,\qquad S_f(A\Vert A)=f(1),\qquad S_f(A\Vert B_k)=\omega(f).$$
--
--   The divergences therefore fail to converge to the value at $A$. This witnesses why the finite-slope assumption is essential.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 9, Remark 2.13

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

/-- Remark 2.13, PDF p.9: nonproportional rank-one approximants witness failure
of second-input continuity at either infinite recession slope. -/
theorem remark_2_13 (hI : 2 ≤ Fintype.card I) (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (hw : recessionSlope f = ⊤ ∨ recessionSlope f = ⊥) (x : I → ℂ) (seq : ℕ → I → ℂ)
    (hx : ∑ i, ‖x i‖ ^ 2 = 1) (hseq : ∀ n, ∑ i, ‖seq n i‖ ^ 2 = 1)
    (hlim : Tendsto seq atTop (𝓝 x))
    (hn : ∀ n, ¬ ∃ c : ℂ, seq n = c • x) :
    let A : Mat I := fun i j => x i * conj (x j)
    let B : ℕ → Mat I := fun n i j => seq n i * conj (seq n j)
    Tendsto B atTop (𝓝 A) ∧ div f A A = (f 1 : EReal) ∧
      (∀ n, div f A (B n) = recessionSlope f) ∧
      ¬ Tendsto (fun n => div f A (B n)) atTop (𝓝 (div f A A)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
