-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_remark_5_7
-- name    : QAlgorithms.Papers.Independent.Support50.P12.remark_5_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:40:31.904618+00:00
-- url     : https://prove2.me/theorems/2130a670-c1c7-4259-ad8b-cb6339d7836c
-- title:
--   Remark 5.7
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   The ten-condition result of Theorem 5.1 holds for co-substochastic maps with co-stochastic/co-substochastic recoveries, after replacing its cocycle by
--
--   $$B^0\Phi^*(\Phi(A)^z\Phi(B)^{-z})=B^{-z}A^z.$$
--
--   The quantifiers are all complex $z$, one real $z\in(0,2)\setminus\{1\}$, or all $z=it$, in conditions (vi)–(viii), respectively. All other conditions and the asymmetric implication chain remain as stated there; two-copositivity supplies the recovery converse. Recovery may retain each given copositivity level or complete copositivity. The proof's adjoint slips are not adopted.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 26, Remark 5.7

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

/-- Remark 5.7, PDF p.26: co-version of the full chain, with reversed products in
(vi)–(viii) and a 2-copositive converse. The proof's Phi/Phi* slips are not copied. -/
theorem remark_5_7 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : CoSubstochastic A B Phi) (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A)
    (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (htr : tr (Phi Y) = tr Y) :
    let c := pairConditions true A B Phi X Y
    (Supports X Y → PairChain c) ∧ (c 1 → c 2) ∧
    (Supports X Y → KCoPositive A Phi 2 → c 9 → c 0) ∧
    (Supports X Y → c 0 →
      (∀ n, KCoPositive A Phi n → ∃ Psi : MatrixMap J I, CoStochastic B A Psi ∧
        KCoPositive B Psi n ∧ Psi (Phi X) = X ∧ Psi (Phi Y) = Y) ∧
      ((∀ n, KCoPositive A Phi n) → ∃ Psi : MatrixMap J I, CoStochastic B A Psi ∧
        (∀ n, KCoPositive B Psi n) ∧ Psi (Phi X) = X ∧ Psi (Phi Y) = Y)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
