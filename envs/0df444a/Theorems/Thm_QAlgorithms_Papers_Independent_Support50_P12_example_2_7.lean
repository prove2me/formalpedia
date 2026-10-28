-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_example_2_7
-- name    : QAlgorithms.Papers.Independent.Support50.P12.example_2_7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:13:15.001014+00:00
-- url     : https://prove2.me/theorems/d5940a83-d96f-4cff-8da8-282c7e2761de
-- title:
--   Example 2.7
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   Put $f_\alpha(x)=x^\alpha$ for $\alpha>0$, and $f_0(x)=1$ for $x>0$, $f_0(0)=0$. Then
--
--   $$S_{f_\alpha}(A\Vert B)=\operatorname{Tr}A^\alpha B^{1-\alpha}+\omega(f_\alpha)\operatorname{Tr}A(I-B^0),\qquad \alpha\ge0.$$
--
--   $$S_{f_\alpha}(A\Vert B)=\begin{cases}\operatorname{Tr}A^\alpha B^{1-\alpha},&0\le\alpha<1\text{ or }A^0\le B^0,\\+\infty,&\alpha>1,\ A^0
--   ot\le B^0.\end{cases}$$
--
--   For $\alpha\ge0$, $\alpha
--   e1$, the Rényi entropy is $(\alpha-1)^{-1}\log S_{f_\alpha}(A\Vert B)$ with the paper's extended logarithm. Also $S_{x\log x}(A\Vert B)$ is $\operatorname{Tr}A(\log^*A-\log^*B)$ on supported pairs and $+\infty$ otherwise. These are Petz, rather than sandwiched, formulas, without trace normalization.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 6, Example 2.7

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

/-- Example 2.7, PDF pp.6–7: support powers, unnormalized Petz Rényi entropy,
and x log x. The alpha=1 identity is retained. -/
theorem example_2_7 [Nonempty I] (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∀ a : ℝ, 0 ≤ a →
      div (supportScalarPower a) A B = (tr (supportPower A a * supportPower B (1 - a)) : EReal) +
        recessionSlope (supportScalarPower a) * (tr (A * (1 - supp B)) : EReal)) ∧
    (∀ a ∈ Ico (0 : ℝ) 1,
      div (supportScalarPower a) A B = (tr (supportPower A a * supportPower B (1 - a)) : EReal)) ∧
    (∀ a : ℝ, 1 < a → div (supportScalarPower a) A B =
      if Supports A B then (tr (supportPower A a * supportPower B (1 - a)) : EReal) else ⊤) ∧
    (∀ a : ℝ, 0 ≤ a → a ≠ 1 →
      petzRenyi a A B = (((a - 1)⁻¹ : ℝ) : EReal) *
        (if div (supportScalarPower a) A B = ⊤ then ⊤ else logNonnegativeExtended (div (supportScalarPower a) A B).toReal)) ∧
    div (fun x => x * Real.log x) A B = relativeEntropy A B := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
