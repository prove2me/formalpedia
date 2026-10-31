-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_upsilonConvexAbove
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.upsilonConvexAbove
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:30:26.270163+00:00
-- url     : https://prove2.me/theorems/b6419bd5-f646-4886-a2ee-3427846103a5
-- title:
--   Lemma 2.1: convexity of Upsilon for q>p
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   If $1\le p\le2$ and $q>p$, then for all $A_0,A_1\ge0$ and $t\in[0,1]$,
--   $$
--   \Upsilon_{p,q}^{B}(tA_0+(1-t)A_1)\le
--    t\Upsilon_{p,q}^{B}(A_0)+(1-t)\Upsilon_{p,q}^{B}(A_1).
--   $$
--   The fixed $B$ can be singular or zero.
--
--   This covers the upper-q part of the main convexity range without adding the proof's dual representation as a hypothesis.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 7, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2.1, PDF pp.7–8, including arbitrary B and singular PSD inputs. -/
theorem upsilonConvexAbove {n : ℕ} (hn : 0 < n) (p q : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hq : p < q) (B : Mat (Fin n)) :
    ConvexOn ℝ (psd (Fin n)) (sandwichedTraceFunctional p q B) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
