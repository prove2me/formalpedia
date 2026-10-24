-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_2_3
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_2_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:11:12.11437+00:00
-- url     : https://prove2.me/theorems/7da00d4d-3249-43c2-aa97-84957aa7d6ba
-- title:
--   Corollary 2.3
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   For spectral projections $P_a$ of $A$ and $Q_b$ of $B$, all three formulas hold:
--
--   $$\begin{aligned}S_f(A\Vert B)&=Q_f(A,B)+\omega(f)\operatorname{Tr}A(I-B^0)\\&=f(0)\operatorname{Tr}B+Q_{f-f(0)}(A,B)+\omega(f)\operatorname{Tr}A(I-B^0)\\&=\sum_a\left[\sum_{b
--   e0}bf(a/b)\operatorname{Tr}P_aQ_b+a\omega(f)\operatorname{Tr}P_aQ_0\right].\end{aligned}$$
--
--   Moreover, $S_f(A\Vert B)=Q_f(A,B)$ exactly when $A^0\le B^0$ or $\omega(f)=0$. Products $0(\pm\infty)$ mean zero. These formulas handle singular inputs without normalizing them.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 6, Corollary 2.3

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

/-- Corollary 2.3, PDF p.6: all three expansions and the exact vanishing criterion. -/
theorem corollary_2_3 [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    div f A B = (quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal) ∧
    div f A B = ((f 0 * tr B + quasi (fun x => f x - f 0) A B : ℝ) : EReal) +
      recessionSlope f * (tr (A * (1 - supp B)) : EReal) ∧
    div f A B = ∑ a ∈ spec A,
      (((∑ b ∈ (spec B).filter (fun b => b ≠ 0),
        b * f (a / b) * tr (spectralProjector A a * spectralProjector B b) : ℝ) : EReal) +
        (a : EReal) * recessionSlope f * (tr (spectralProjector A a * spectralProjector B 0) : EReal)) ∧
    (div f A B = (quasi f A B : EReal) ↔ Supports A B ∨ recessionSlope f = 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
