-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_phiImpliesTraceProduct
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.phiImpliesTraceProduct
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:38:16.883026+00:00
-- url     : https://prove2.me/theorems/c401fbe1-3350-4b66-abac-19163667fd31
-- title:
--   Lemma 5.1: Phi implies trace-product convexity/concavity, corrected from proof
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   Fix a positive dimension. For $1\le p\le2$, joint convexity of the binary map $(A,B)\mapsto\Phi_{p,1}(A,B)$ on the PSD pairs implies joint convexity of $\operatorname{Tr}(A^pB^{1-p})$ on $A\ge0,B>0$. For $0<p\le1$, joint concavity of that binary map implies joint concavity of the trace product on all PSD pairs:
--   $$
--   \operatorname{Convex}\Phi_{p,1}\ \Longrightarrow\
--   \operatorname{Convex}\bigl[\operatorname{Tr}(A^pB^{1-p})\bigr],\qquad
--   \operatorname{Concave}\Phi_{p,1}\ \Longrightarrow\
--   \operatorname{Concave}\bigl[\operatorname{Tr}(A^pB^{1-p})\bigr].
--   $$
--   These are conditional implications, not assumptions of the trace-product conclusion.
--
--   This records the implication proved by the source's Taylor argument.
--
--   **Source correction.** The printed lemma uses $1-1/p$ and an unused $q$; equations (5.1) and (5.3)–(5.5) use $1-p$. This statement follows those equations and removes $q$. At $p=2$ the intended scalar perspective is $a^2/b$, while the printed $a^2\sqrt b$ is not convex.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 14, Lemma 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 5.1, PDF pp.14–15, corrected from (5.1),(5.3)–(5.5).
Printed B^(1-1/p) is changed to B^(1-p), and the unused q is removed.
The proof explicitly uses 1-p; at p=2 it gives A^2/B, whereas the printed
scalar A^2 sqrt(B) is not jointly convex. Independent moderation is required. -/
theorem phiImpliesTraceProduct {n : ℕ} (hn : 0 < n) (p : ℝ) :
    (1 ≤ p → p ≤ 2 →
      ConvexOn ℝ (psdPairs (Fin n)) (binaryPhi p 1) →
      ConvexOn ℝ (regularPairs (Fin n)) (traceProduct p p)) ∧
    (0 < p → p ≤ 1 →
      ConcaveOn ℝ (psdPairs (Fin n)) (binaryPhi p 1) →
      ConcaveOn ℝ (psdPairs (Fin n)) (traceProduct p p)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
