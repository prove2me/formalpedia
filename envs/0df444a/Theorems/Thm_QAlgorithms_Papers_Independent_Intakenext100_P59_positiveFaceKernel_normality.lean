-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P59_positiveFaceKernel_normality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P59.positiveFaceKernel_normality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:48:57.844923+00:00
-- url     : https://prove2.me/theorems/35d2cd13-ea72-4cc7-b7bb-93fe8578b1cf
-- title:
--   Normal zeroth-face image and positive-face preservation of the kernel chain
-- statement:
--   Let $G$ be a simplicial group, with degree-$n$ group $G_n$ and face maps $d_i$. Set $\overline G_0=\{1\}$ and, for $n\geq1$, let
--
--   $$
--   \overline G_n=\ker(d_1\circ d_2\circ\cdots\circ d_n:G_n\to G_0).
--   $$
--
--   For every integer $n\geq0$, the image of $\overline G_{n+1}$ under $d_0$ is a normal subgroup of $G_n$, and every positive face preserves the kernel chain:
--
--   $$
--   d_0(\overline G_{n+1})\trianglelefteq G_n,\qquad
--   d_i(\overline G_{n+1})\subseteq\overline G_n\quad(1\leq i\leq n+1).
--   $$
--
--   This identifies the elementary subgroup properties used before the additional crossed-action assumption in Section 3.
--
--   **Formalization Note** The composite of the positive faces is restriction to the first vertex. It is encoded by the simplicial map induced by the order-preserving inclusion $[0]\to[n]$ with value $0$, rather than by an intersection of individual face kernels.
-- source:
--   Crossed Module Bundle Gerbes; Classification, String Group and Differential Geometry, arXiv:math/0510078v2, PDF p. 7, Section 3, opening paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P59

open CategoryTheory

open scoped Simplicial

universe u

namespace QAlgorithms.Papers.Independent.Intakenext100.P59

/-- Section 3 opening, PDF p. 7: the zeroth-face image is normal, and every
positive face maps Gbar_(n+1) into Gbar_n. Includes n=0 with Gbar_0 trivial;
no crossed action, smoothness, or vanishing homotopy is needed for this
algebraic claim, which precedes those additional assumptions in the source. -/
theorem positiveFaceKernel_normality
    (G : SimplicialObject GrpCat.{u}) (n : ℕ) :
    (boundaryImage G n).Normal ∧
      ∀ (i : Fin (n + 2)), 0 < i.val →
        ∀ g : GroupLevel G (n + 1), g ∈ positiveFaceKernel G (n + 1) →
          (G.δ (n := n) i).hom g ∈ positiveFaceKernel G n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P59
