-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_generating_set
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_generating_set
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:13:27.084381+00:00
-- url     : https://prove2.me/theorems/112cd3ea-60ea-42c6-a580-be6dd1b88bb3
-- title:
--   Lemma 5.8
-- statement:
--   Let $S\subseteq k^d$ be arbitrary, with the trace Borel sigma algebra, and let $E\subseteq M(S)$ have the eight properties of the intertwining-set theorem. Denote the restricted coordinates by $z_j$ and set $|z|^2=\sum_j|z_j|^2$. Then
--
--   $$\begin{aligned}
--   E=M(S)&\Longleftrightarrow (\forall j)\ z_j\in E\\
--   &\Longleftrightarrow (\forall j)\ \frac{z_j}{1+|z|^2}\in E\quad\text{and}\quad\frac1{1+|z|^2}\in E\\
--   &\Longleftrightarrow (\forall j)\ \frac{z_j}{\sqrt{1+|z|^2}}\in E.
--   \end{aligned}$$
--
--   The eight assumed properties are exactly those stated here:
--
--   The eight properties are: (1) $E$ is a unital $k$-linear star subalgebra; (2) $f^{-1}\in E$ for every nowhere-zero $f\in E$; (3) $f\in E$ if and only if both $f/(1+|f|^2)$ and $1/(1+|f|^2)$ belong to $E$; (4) $E$ is closed under arbitrary sequential pointwise limits in $M(X)$; (5) $f\in E$ implies $|f|\in E$; (6) real-valued $f,g\in E$ have $f\vee g,f\wedge g\in E$; (7) the measurable sets $A$ with $1_A\in E$ form a sub-sigma-algebra of $\Sigma$; (8) $f\in E$ implies $1_{f^{-1}(B)}\in E$ for every Borel subset $B$ of $k$.
--
--   This identifies small generating families for equality of calculi.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 23, Lemma 5.8

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Lemma 5.8, PDF p.23: four equivalent generating conditions on the intended trace-Borel base X.
Source correction (independently audited in moderation round 1).
Printed: Lemma 5.8 starts with E subset M(K^d), but condition (i) uses M(X,Sigma) and the section defines coordinates restricted to X subset K^d.
Changed: Use E subset M(S) for an arbitrary S subset k^d with its trace Borel sigma algebra, and use the restricted coordinates throughout.
Why: This is the base fixed by the section preamble and the generating-sigma-algebra proof, and is the version needed by Theorem 5.9. No measurability or closedness of S is added; all four equivalent conditions are retained.
-/
theorem calculus_generating_set {d : ℕ} (S : Set (Fin d → k)) (E : Set (Symbol S k))
    (hE : EightProperties E) :
    ((E = Set.univ) ↔ ∀ j, restrictedCoordinate S j ∈ E) ∧
    ((E = Set.univ) ↔ (∀ j, times (restrictedCoordinate S j) (tupleRegularizer S) ∈ E) ∧ tupleRegularizer S ∈ E) ∧
    ((E = Set.univ) ↔ ∀ j, tupleRootCoordinate S j ∈ E) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
