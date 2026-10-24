-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_theorem_7_1
-- name    : QAlgorithms.Papers.Independent.Support50.P12.theorem_7_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:08:56.311702+00:00
-- url     : https://prove2.me/theorems/acc669f4-a478-4230-b524-73ab98c9b0ed
-- title:
--   Abstract main result (p.1), pinned to Theorem 7.1
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$. Let $C$ be a nonempty set of density operators in $\mathcal A_1$. Write $\overline{\operatorname{co}}C$ for its closed convex hull, $P_C$ for its joined support, and $d^2=(\dim H_1)^2+(\dim H_2)^2$.
--
--   If $\Phi$ is trace preserving and two-positive, the following are equivalent: (i) one stochastic $\Psi$ recovers every state in the closed convex hull; (ii) every operator convex $f$ preserves every pair's divergence on that hull; (iii) one reference density $\sigma$ with support covering $P_C$ and one operator convex $f$ with $|\operatorname{supp}\mu_f|\ge d^2$ preserve $S_f(\rho\Vert\sigma)$ for all $\rho\in C$; (iv) one such reference and one $T\subset(0,\infty)$, $|T|\ge d^2$, preserve all $S_{\varphi_t}$ for every code state, where $\varphi_t(x)=-x/(x+t)$; (v) all $H_r$ preserve every pair on the hull for every real $r$; (vi) one covering reference and one $\delta>0$ give preservation for all code states and all $0<r<\delta$; (vii) every hull state is recovered by $\Phi_\sigma^*$ for every hull reference with support exactly $P_C$; (viii) one density reference has that recovery property for all code states; (ix) the input/output code supports have shared orthogonal tensor-block decompositions with invertible right density operators $\omega_k,\widetilde\omega_k$ and left unitaries $U_k$, such that every code state is $\bigoplus_kp_k\rho_{k,L}\otimes\omega_k$ and
--
--   $$\Phi(X\otimes\omega_k)=U_kXU_k^*\otimes\widetilde\omega_k\qquad(X\in B(H_{1,k,L})).$$
--
--   The same recovery can retain each given $n$-positivity level of $\Phi$, or complete positivity. For merely substochastic $\Phi$, $(i)\Rightarrow(ii)\Rightarrow(iii)\Rightarrow(iv)\Rightarrow(viii)$ still holds. Finally, (x) one covering density reference $\sigma$ gives
--
--   $$T_p(\Phi^{\otimes n}(\rho^{\otimes n})\Vert\Phi^{\otimes n}(\sigma^{\otimes n}))=T_p(\rho^{\otimes n}\Vert\sigma^{\otimes n})\quad(\rho\in C,\ 0<p<1,\ n\in\mathbb N),$$
--
--   where $T_p=-\log(P_{\rm opt}/\min(p,1-p))$, is sufficient for (i)–(viii), and necessary when $\Phi$ is completely positive. References, generators, parameter sets and block data are chosen before all states being tested. This is the full error-correction equivalence.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 33, Theorem 7.1 (abstract main result)

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

/-- Theorem 7.1, PDF pp.33–34 (abstract p.1): all nine equivalences, all uniform
choices, both positivity refinements, the substochastic chain, and criterion (x).
The bound is dim(H1)^2+dim(H2)^2. -/
theorem theorem_7_1 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hc : AlgebraExtension A B Phi) (C : Set (Mat I)) (hn : C.Nonempty) (hC : ∀ rho ∈ C, AlgebraDensity A rho) :
    let c := codeConditions A B Phi C
    ((AlgebraTracePreserving A Phi ∧ AlgebraKPositive A Phi 2) →
      (∀ i : Fin 9, c (Fin.castSucc i) ↔ c 0) ∧
      (c 0 → RecoveryRefinement A B Phi (hull C)) ∧
      (c 9 → ∀ i : Fin 8, c (Fin.castLE (by omega : 8 ≤ 10) i)) ∧
      (AlgebraCompletelyPositive A Phi → (c 0 ↔ c 9))) ∧
    (Substochastic A B Phi → (c 0 → c 1) ∧ (c 1 → c 2) ∧ (c 2 → c 3) ∧ (c 3 → c 7)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
