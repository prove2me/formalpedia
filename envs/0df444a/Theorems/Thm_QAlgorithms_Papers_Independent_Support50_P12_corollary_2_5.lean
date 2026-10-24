-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_2_5
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_2_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:12:13.655613+00:00
-- url     : https://prove2.me/theorems/022bde46-7e51-4334-b4f2-e06b4df6703e
-- title:
--   Corollary 2.5
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   For $\lambda\ge0$, mutually orthogonal support joins of two positive pairs, any linear or anti-linear isometry $V:H\to K$, and any unit vector $x\in K$, respectively,
--
--   $$\begin{gathered}S_f(\lambda A\Vert\lambda B)=\lambda S_f(A\Vert B),\\S_f(A_1+A_2\Vert B_1+B_2)=S_f(A_1\Vert B_1)+S_f(A_2\Vert B_2),\\S_f(VAV^*\Vert VBV^*)=S_f(A\Vert B),\\S_f(A\otimes|x\rangle\langle x|\Vert B\otimes|x\rangle\langle x|)=S_f(A\Vert B).\end{gathered}$$
--
--   In the sum identity the hypothesis is $(A_1^0\vee B_1^0)\perp(A_2^0\vee B_2^0)$. Zero scaling is included. These are the basic covariance and direct-sum rules.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 6, Corollary 2.5

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

/-- Corollary 2.5, PDF p.6: zero scaling, orthogonal sums, both sorts of isometry,
and tensoring with any unit-vector projection. -/
theorem corollary_2_5 [Nonempty I] [Nonempty J] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B A1 B1 A2 B2 : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hA1 : A1.PosSemidef) (hB1 : B1.PosSemidef)
    (hA2 : A2.PosSemidef) (hB2 : B2.PosSemidef) :
    (∀ l : ℝ, 0 ≤ l → div f ((l : ℂ) • A) ((l : ℂ) • B) = (l : EReal) * div f A B) ∧
    ((A1 + B1) * (A2 + B2) = 0 →
      div f (A1 + A2) (B1 + B2) = div f A1 B1 + div f A2 B2) ∧
    (∀ (anti : Bool) (W : Matrix J I ℂ), Wᴴ * W = 1 →
      div f (isometricConjugation anti W A) (isometricConjugation anti W B) = div f A B) ∧
    (∀ x : J → ℂ, ∑ j, ‖x j‖ ^ 2 = 1 →
      div f (Matrix.kronecker A (fun i j => x i * conj (x j)))
        (Matrix.kronecker B (fun i j => x i * conj (x j))) = div f A B) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
