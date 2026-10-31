-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_traceFunctionClassification
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.traceFunctionClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:26:14.693161+00:00
-- url     : https://prove2.me/theorems/9823ceb9-5b0d-4c73-b8bb-3e1e9e214b6c
-- title:
--   Theorem 1.1: convexity, concavity, and failure beyond p=2
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   For $1\le p\le2$ and $q\ge1$, all three functionals are convex, jointly in the tuple for $\Phi$. For $0<p\le q\le1$ they are concave, jointly for $\Phi$. For $p>2$, $q>0$, $q\ne p$, each of the three dimension families fails both convexity and concavity:
--   $$
--   \neg\mathcal C_\Upsilon\ \land\ \neg\mathcal K_\Upsilon\ \land\
--   \neg\mathcal C_\Psi\ \land\ \neg\mathcal K_\Psi\ \land\
--   \neg\mathcal C_\Phi\ \land\ \neg\mathcal K_\Phi.
--   $$
--   Here $\mathcal C$ and $\mathcal K$ mean respectively convexity and concavity for every positive finite dimension (and every fixed $B$ for $\Upsilon$). Each failure therefore has some finite-dimensional witness; failure is not required for every dimension or every $B$.
--
--   This classifies the ranges established by the paper, including its negative conclusion.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 2, Theorem 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1.1, PDF pp.2,13. The proof uses 0<p for concavity. Failure
beyond p=2 is somewhere in each dimension-free family, not for every n,m,B. -/
theorem traceFunctionClassification :
    (∀ p q : ℝ, 1 ≤ p → p ≤ 2 → 1 ≤ q →
      UConvex p q ∧ PsiConvex p q ∧ PhiConvex p q) ∧
    (∀ p q : ℝ, 0 < p → p ≤ q → q ≤ 1 →
      UConcave p q ∧ PsiConcave p q ∧ PhiConcave p q) ∧
    (∀ p q : ℝ, 2 < p → 0 < q → q ≠ p →
      ¬ UConvex p q ∧ ¬ UConcave p q ∧ ¬ PsiConvex p q ∧
      ¬ PsiConcave p q ∧ ¬ PhiConvex p q ∧ ¬ PhiConcave p q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
