-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_lemma_4_4
-- name    : TemperleyLieb.Gram.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:41.373314+00:00
-- url     : https://prove2.me/theorems/9d6b1ed2-af08-48df-bbab-50a106d44965
-- title:
--   Lemma 4.4, p. 17 — triangular orthogonal seminormal basis
-- statement:
--   Over $F=\operatorname{Frac}(\mathbb Z[x])$, form $f_t=m_tF_t$ from the paper's spectral projector. For each shape $\lambda$, the vectors are triangular in the Murphy basis, form a basis of the cell module, and are pairwise orthogonal. They also diagonalize $T_k$ and $z_k$:
--
--   $$f_t=m_t+\sum_{u\triangleright t}a_um_u,\qquad \langle f_s,f_t\rangle=0\ (s\ne t),\qquad f_tT_k=r_t(k)f_t,\quad f_tz_k=z_t(k)f_t.$$
--
--   The basis and orthogonality permit the Gram determinant to be computed from the norms of the $f_t$.
--
--   **Formalization Note** The paper prints $\langle f_s,f_t\rangle=\delta_{s,t}$ in part (3). This is false for $n=2$ because the nonzero diagonal norm is $x$; the theorem states the orthogonality used later. The existence of the field Murphy datum and its specified JM family is explicit. The projector ranges over contents from all shapes, as on p. 17.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 17, Lemma 4.4 and definition of F_t

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Enyang, Lemma 4.4, p. 17. Part (3) is orthogonality, correcting the
printed Kronecker delta, which contradicts the paper's later norm formula. -/
theorem lemma_4_4 (n : ℕ) (hn : 1 ≤ n) :
    ∃ D : FDatum n, IsMurphyDatum F xF n D ∧
      ∃ J : JMFamily D (n + 1), IsPaperJMFamily n D J ∧
        ∀ f : Fin (n / 2 + 1),
          (∀ t : Tab n f, ∃ a : Tab n f → F,
            seminormalVector J f t = cellVector f t +
              ∑ u ∈ Finset.univ.filter (fun u : Tab n f => t < u),
                a u • cellVector f u) ∧
          (∃ B : Module.Basis (Tab n f) F (Tab n f → F),
            ∀ t, B t = seminormalVector J f t) ∧
          (∀ s t : Tab n f, s ≠ t →
            cellForm D f (seminormalVector J f s) (seminormalVector J f t) = 0) ∧
          (∀ (t : Tab n f) (k : Fin (n + 1)),
            cellAct D f (seminormalVector J f t) (JM F xF n k) =
              rF t k • seminormalVector J f t ∧
            cellAct D f (seminormalVector J f t) (zJM F xF n k) =
              ztF t k • seminormalVector J f t) := by sorry

end TemperleyLieb.Gram
