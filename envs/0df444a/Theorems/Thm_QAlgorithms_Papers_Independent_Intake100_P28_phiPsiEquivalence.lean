-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_phiPsiEquivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.phiPsiEquivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:36:43.065545+00:00
-- url     : https://prove2.me/theorems/de226a82-7cf4-457a-9b6f-7038e4308f18
-- title:
--   Remark 3.3: equivalence of the Phi and Psi convexity/concavity families
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   Fix $p,q>0$. Let $\mathcal C_\Phi$ denote joint convexity of $\Phi$ for every positive tuple length and matrix dimension, and let $\mathcal C_\Psi$ denote convexity of $\Psi$ for every pair of positive factor dimensions. Define $\mathcal K_\Phi,\mathcal K_\Psi$ analogously for concavity. Then
--   $$
--   \mathcal C_\Phi\Longleftrightarrow\mathcal C_\Psi,\qquad
--   \mathcal K_\Phi\Longleftrightarrow\mathcal K_\Psi.
--   $$
--   In addition, for every positive tuple $A_1,\ldots,A_m$, form $D$ on $\mathbb C^n\otimes\mathbb C^m$ with coefficients $D_{(a,j),(b,k)}=\delta_{jk}(A_j)_{ab}$. Then
--   $$
--   \Psi_{p,q}(D)=\Phi_{p,q}(A_1,\ldots,A_m).
--   $$
--   The classical label is in the traced second factor.
--
--   This identifies the convexity and concavity properties of the two entire families.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 12, Remark 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark 3.3, PDF pp.11–12: equivalence of entire dimension families,
with the classical block label on the traced factor. -/
theorem phiPsiEquivalence (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (PhiConvex p q ↔ PsiConvex p q) ∧ (PhiConcave p q ↔ PsiConcave p q) ∧
    (∀ m n : ℕ, 0 < m → 0 < n → ∀ A ∈ tuples m n,
      partialTraceFunctional p q (classicalBlock A) = tupleTraceFunctional p q A) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
