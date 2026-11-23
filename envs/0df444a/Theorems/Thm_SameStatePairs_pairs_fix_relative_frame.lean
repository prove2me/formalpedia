-- Prove2me | Theorems.Thm_SameStatePairs_pairs_fix_relative_frame
-- name    : SameStatePairs.pairs_fix_relative_frame
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T21:06:03.590348+00:00
-- url     : https://prove2.me/theorems/02ad7a2c-96b4-43e7-8e00-70be3f6e2409
-- title:
--   Theorem 2 (noise-free part): synchronized pairs fix the relative rotation exactly at rank $k$
-- statement:
--   Let $(x_i,y_i)_{i=1}^m$ be pairs in $\mathbb{R}^k$ with $y_i=Qx_i$ for an unknown $Q\in O(k)$, let $\mathbf X=[x_1,\dots,x_m]^\top$ and $r=\operatorname{rank}(\mathbf X)$.
--
--   1. If $r=k$, $Q$ is the unique minimiser over $R\in O(k)$ of the orthogonal Procrustes objective $\sum_i\|y_i-Rx_i\|^2$.
--   2. If $r<k$, let $U\in O(k)$ be an orthonormal basis whose first $r$ vectors span the row space of $\mathbf X$. Then the set of $R\in O(k)$ with $\mathbf XR^\top=\mathbf Y$ is
--   $$\{\,QU(I_r\oplus S)U^\top:\ S\in O(k-r)\,\},$$
--   that is, $Q(I_r\oplus O(k-r))$ written in the basis $U$.
--   3. If $r=k-1$, this set has exactly two elements, $Q$ and a matrix $R$ with $\det(Q^\top R)=-1$, a reflection on the one-dimensional complement.
--
--   **Formalization Note** The noisy part of Theorem 2 (the $O_P(\sigma\sqrt{k/m_e})$ rate for a sufficiently large unspecified constant $c_0$) and the count of $(k-r)(k-r-1)/2$ continuous gauge dimensions (the dimension of $O(k-r)$) are not included. The phrase "in an orthonormal basis whose first $r$ vectors span the row space" is written as conjugation by an orthogonal $U$ with that property, for every such $U$.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 4.2, Theorem 2, p. 7; proof in Appendix A.2, pp. 11-12

import Mathlib
import Definitions.Def_SameStatePairs_Basic

open Matrix

namespace SameStatePairs

theorem pairs_fix_relative_frame {m k : ℕ} (x y : Fin m → Fin k → ℝ)
    (Q : Matrix.orthogonalGroup (Fin k) ℝ) (hy : ∀ i, y i = rot Q (x i)) :
    ((Matrix.of x).rank = k →
      ∀ R : Matrix.orthogonalGroup (Fin k) ℝ,
        (∀ R' : Matrix.orthogonalGroup (Fin k) ℝ, procrustesObj x y R ≤ procrustesObj x y R') ↔
          R = Q) ∧
    ((Matrix.of x).rank < k →
      ∀ U : Matrix.orthogonalGroup (Fin k) ℝ,
        Submodule.span ℝ ((fun j : Fin k => fun i => (U : Matrix (Fin k) (Fin k) ℝ) i j) ''
            {j | j.val < (Matrix.of x).rank}) = Submodule.span ℝ (Set.range x) →
        pairSolutions x y = {R : Matrix.orthogonalGroup (Fin k) ℝ | ∃ S : Matrix.orthogonalGroup (Fin (k - (Matrix.of x).rank)) ℝ,
          (R : Matrix (Fin k) (Fin k) ℝ) = (Q : Matrix (Fin k) (Fin k) ℝ) *
            (U : Matrix (Fin k) (Fin k) ℝ) *
              blockEmbed (Matrix.of x).rank (S : Matrix _ _ ℝ) *
                (U : Matrix (Fin k) (Fin k) ℝ)ᵀ}) ∧
    ((Matrix.of x).rank + 1 = k →
      (pairSolutions x y).ncard = 2 ∧
      ∀ R ∈ pairSolutions x y, R ≠ Q →
        ((Q : Matrix (Fin k) (Fin k) ℝ)ᵀ * (R : Matrix (Fin k) (Fin k) ℝ)).det = -1) := by sorry

end SameStatePairs
