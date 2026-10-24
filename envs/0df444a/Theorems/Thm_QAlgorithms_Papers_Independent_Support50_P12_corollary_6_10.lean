-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_6_10
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_6_10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:48:07.90299+00:00
-- url     : https://prove2.me/theorems/8b9cd0db-d6f6-4fe2-a69f-680e0ed6ded7
-- title:
--   Corollary 6.10
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   Assume $\Phi$ is substochastic, $\operatorname{Tr}\Phi(B)=\operatorname{Tr}B$, $A^0=B^0$, and $\operatorname{Tr}A=\operatorname{Tr}B$. Then
--
--   $$C(\Phi(A)\Vert\Phi(B))=C(A\Vert B)\quad\Longrightarrow\quad\Phi_B^*(\Phi(A))=A.$$
--
--   This replaces, rather than inherits, the interior-preservation disjunction. The zero pair is included.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 32, Corollary 6.10

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

/-- Corollary 6.10, PDF p.32: equal supports and traces replace the interior
hypothesis; the zero pair is included. -/
theorem corollary_6_10 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A)
    (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (hs : supp X = supp Y)
    (htrace : tr X = tr Y) (htr : tr (Phi Y) = tr Y)
    (heq : chernoff (Phi X) (Phi Y) = chernoff X Y) :
    petz Y Phi (Phi X) = X := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
