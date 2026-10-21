-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_finite_operations
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_finite_operations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:02:19.53299+00:00
-- url     : https://prove2.me/theorems/f6e2c172-5d4d-4343-bce4-197e278839c9
-- title:
--   Remark 2.5
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $d\ge0$ and let $f_1,\ldots,f_d\in M(X)$. Their domain intersection is a core for every operator in the tuple, and
--
--   $$\overline{\sum_{j=1}^d\Phi(f_j)}=\Phi\!\left(\sum_{j=1}^df_j\right),\qquad\overline{\Phi(f_1)\cdots\Phi(f_d)}=\Phi(f_1\cdots f_d).$$
--
--   An empty sum is the full-domain zero, an empty product is the identity, and an empty intersection is $H$.
--
--   This is the finite-family version of the two-operator closure statements.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 10, Remark 2.5

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

/-- Remark 2.5, PDF p.10: finite intersections of domains and boundedGraph closures of finite operations. -/
theorem calculus_finite_operations (F : Symbol X k → Relation H) (hF : Calculus F)
    {d : ℕ} (f : Fin d → Symbol X k) :
    (∀ j, GraphCore (F (f j)) (⋂ i, graphDomain (F (f i)))) ∧
    closure (sumGraphs ((List.finRange d).map fun j => F (f j))) = F (tupleSum f) ∧
    closure (productGraphs ((List.finRange d).map fun j => F (f j))) = F (tupleProduct f) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
