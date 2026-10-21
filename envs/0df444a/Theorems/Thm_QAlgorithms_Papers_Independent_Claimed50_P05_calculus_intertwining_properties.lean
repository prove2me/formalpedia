-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_intertwining_properties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_intertwining_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:12:21.63482+00:00
-- url     : https://prove2.me/theorems/0f3fd792-8672-431a-9a48-f713bdf209cc
-- title:
--   Theorem 5.3
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $K$ be another Hilbert space, let $\Psi:M(X)\to C(K)$ be a measurable calculus, and let $T:H\to K$ be bounded. Define
--
--   $$E=\{f\in M(X):T\Phi(f)\subseteq\Psi(f)T\}.$$
--
--   Equivalently, every $(x,y)\in\Phi(f)$ satisfies $(Tx,Ty)\in\Psi(f)$. This set has all eight properties below.
--
--   The eight properties are: (1) $E$ is a unital $k$-linear star subalgebra; (2) $f^{-1}\in E$ for every nowhere-zero $f\in E$; (3) $f\in E$ if and only if both $f/(1+|f|^2)$ and $1/(1+|f|^2)$ belong to $E$; (4) $E$ is closed under arbitrary sequential pointwise limits in $M(X)$; (5) $f\in E$ implies $|f|\in E$; (6) real-valued $f,g\in E$ have $f\vee g,f\wedge g\in E$; (7) the measurable sets $A$ with $1_A\in E$ form a sub-sigma-algebra of $\Sigma$; (8) $f\in E$ implies $1_{f^{-1}(B)}\in E$ for every Borel subset $B$ of $k$.
--
--   This controls intertwiners under algebraic operations and measurable limits.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 20, Theorem 5.3

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

/-- Theorem 5.3, PDF pp.20–22: all eight properties of the concrete intertwining set. -/
theorem calculus_intertwining_properties (F : Symbol X k → Relation H) (G : Symbol X k → Relation K)
    (hF : Calculus F) (hG : Calculus G) (T : H →L[k] K) :
    EightProperties {f | Intertwines F G T f} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
