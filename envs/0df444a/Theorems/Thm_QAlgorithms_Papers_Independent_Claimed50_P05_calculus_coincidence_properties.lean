-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_coincidence_properties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_coincidence_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:13:05.311511+00:00
-- url     : https://prove2.me/theorems/b3bc1e7b-2188-4817-8916-333388091262
-- title:
--   Corollary 5.6
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   For another measurable calculus $\Psi$ on the same $X$ and $H$, define the exact graph-coincidence set
--
--   $$E=\{f\in M(X):\Phi(f)=\Psi(f)\}.$$
--
--   It has all eight properties below.
--
--   The eight properties are: (1) $E$ is a unital $k$-linear star subalgebra; (2) $f^{-1}\in E$ for every nowhere-zero $f\in E$; (3) $f\in E$ if and only if both $f/(1+|f|^2)$ and $1/(1+|f|^2)$ belong to $E$; (4) $E$ is closed under arbitrary sequential pointwise limits in $M(X)$; (5) $f\in E$ implies $|f|\in E$; (6) real-valued $f,g\in E$ have $f\vee g,f\wedge g\in E$; (7) the measurable sets $A$ with $1_A\in E$ form a sub-sigma-algebra of $\Sigma$; (8) $f\in E$ implies $1_{f^{-1}(B)}\in E$ for every Borel subset $B$ of $k$.
--
--   This gives measurable closure properties of equality between calculi.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 22, Corollary 5.6

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

/-- Corollary 5.6, PDF p.22: the exact coincidence set has all eight properties. -/
theorem calculus_coincidence_properties (F G : Symbol X k → Relation H)
    (hF : Calculus F) (hG : Calculus G) : EightProperties {f | F f = G f} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
