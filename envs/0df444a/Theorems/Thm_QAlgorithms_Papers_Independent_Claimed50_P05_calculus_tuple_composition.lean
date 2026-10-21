-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_tuple_composition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_tuple_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:14:46.980274+00:00
-- url     : https://prove2.me/theorems/9e4699ef-0f42-4234-bd84-4c3cff16bd6f
-- title:
--   Proposition 5.11
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $\Psi$ be a measurable calculus on another base $(Y,\Sigma_Y)$ acting on the same $H$. Let $f_1,\ldots,f_d\in M(X)$ and $g_1,\ldots,g_d\in M(Y)$ satisfy $\Phi(f_j)=\Psi(g_j)$ for every $j$. Then, for every finite-valued Borel $h:k^d\to k$,
--
--   $$\Phi(h\circ(f_1,\ldots,f_d))=\Psi(h\circ(g_1,\ldots,g_d)).$$
--
--   Neither $h$ nor the component functions need be bounded.
--
--   This proves that measurable joint functions depend only on the coordinate operators.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 24, Proposition 5.11

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

/-- Proposition 5.11, PDF p.24: equal restrictedCoordinate images give equality for every measurable symbol h. -/
theorem calculus_tuple_composition {d : ℕ} (F : Symbol X k → Relation H)
    (G : Symbol Y k → Relation H) (hF : Calculus F) (hG : Calculus G)
    (f : Fin d → Symbol X k) (g : Fin d → Symbol Y k) (h : ∀ j, F (f j) = G (g j))
    (a : Symbol (Fin d → k) k) :
    F (compose a (fun x j => (f j).val x) (measurable_pi_lambda _ fun j => (f j).property)) =
      G (compose a (fun x j => (g j).val x) (measurable_pi_lambda _ fun j => (g j).property)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
