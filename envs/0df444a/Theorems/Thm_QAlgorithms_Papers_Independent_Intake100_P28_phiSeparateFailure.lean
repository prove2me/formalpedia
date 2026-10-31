-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_phiSeparateFailure
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.phiSeparateFailure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:37:27.264411+00:00
-- url     : https://prove2.me/theorems/6802f77b-0ad4-4900-937b-db47a59bc139
-- title:
--   Lemma 3.4: neither convex nor concave beyond p=2
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   For every $p>2$ and $q>0$ with $q\ne p$, there is a positive matrix dimension and a fixed positive semidefinite $B$ for which $A\mapsto\Phi_{p,q}(A,B)$ fails convexity; there is also such a dimension and fixed $B$ for failure of concavity:
--   $$
--   \exists n\ge1,\ B\ge0:\ \neg\operatorname{Convex}_{A\ge0}\Phi_{p,q}(A,B),\qquad
--   \exists n\ge1,\ B\ge0:\ \neg\operatorname{Concave}_{A\ge0}\Phi_{p,q}(A,B).
--   $$
--   The witnesses can differ. The second argument stays fixed within each Jensen test.
--
--   Thus even separate convexity and concavity fail somewhere in the matrix family beyond $p=2$.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 12, Lemma 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3.4, PDF pp.12–13: binary Phi already fails separately in some
finite dimension with a fixed second argument. The proof's general-q display
has a typo Phi_{p,1}; this statement keeps Phi_{p,q}. -/
theorem phiSeparateFailure (p q : ℝ) (hp : 2 < p) (hq : 0 < q) (hqp : q ≠ p) :
    (∃ n : ℕ, 0 < n ∧ ∃ B ∈ psd (Fin n),
      ¬ ConvexOn ℝ (psd (Fin n)) (fun A => binaryPhi p q (A,B))) ∧
    (∃ n : ℕ, 0 < n ∧ ∃ B ∈ psd (Fin n),
      ¬ ConcaveOn ℝ (psd (Fin n)) (fun A => binaryPhi p q (A,B))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
