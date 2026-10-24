-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_theorem_5_1
-- name    : QAlgorithms.Papers.Independent.Support50.P12.theorem_5_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:38:15.000252+00:00
-- url     : https://prove2.me/theorems/cf91c169-9c26-4399-b1dd-b358920435dc
-- title:
--   Theorem 5.1
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   Assume $\Phi$ is substochastic and preserves the trace of $B$. For $A^0\le B^0$, define ten conditions: (i) one stochastic map recovers both $A,B$; (ii) one substochastic map does so; (iii) every operator convex $f$ has its divergence preserved; (iv) one such $f$ does so with representing-measure support cardinal at least $|\operatorname{spec}\Delta\cup\operatorname{spec}\widetilde\Delta|$; (v) one set $T\subset(0,\infty)$ of at least this cardinal has every $S_{\varphi_t}$ preserved, where $\varphi_t(x)=-x/(x+t)$ and $\Delta=L_AR_{B^{-1}}$, $\widetilde\Delta=L_{\Phi(A)}R_{\Phi(B)^{-1}}$ on their actual algebras. Conditions (vi), (vii), and (viii) are $B^0\Phi^*(\Phi(B)^{-z}\Phi(A)^z)=B^{-z}A^z$ for all complex $z$, for some real $z\in(0,2)\setminus\{1\}$, and for all imaginary $z=it$, respectively. Condition (ix) is $B^0\Phi^*(\log^*\Phi(A)-(\log^*\Phi(B))\Phi(A)^0)=\log^*A-(\log^*B)A^0$; (x) is $\Phi_B^*(\Phi(A))=A$. Then
--
--   $$(i)\Rightarrow(ii)\Rightarrow(iii)\Rightarrow(iv)\Leftrightarrow(v)\Leftrightarrow(vi)\Leftrightarrow(vii)\Leftrightarrow(viii)\Leftrightarrow(ix)\Rightarrow(x).$$
--
--   Two-positivity of $\Phi$ also gives $(x)\Rightarrow(i)$. The implication $(ii)\Rightarrow(iii)$ needs no support inclusion. When recovery (i) exists, it can preserve every given $n$-positivity level of $\Phi$, or complete positivity. These are equivalences only in the indicated stronger map regime.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 21, Theorem 5.1

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

/-- Theorem 5.1, PDF pp.21–25: complete ten-condition chain and both positivity
refinements. Only the chain needs support inclusion; (ii)=>(iii) does not. -/
theorem theorem_5_1 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A)
    (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (htr : tr (Phi Y) = tr Y) :
    let c := pairConditions false A B Phi X Y
    (Supports X Y → PairChain c) ∧ (c 1 → c 2) ∧
    (Supports X Y → AlgebraKPositive A Phi 2 → c 9 → c 0) ∧
    (Supports X Y → c 0 → RecoveryRefinement A B Phi {X, Y}) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
