-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_lemma_2_3
-- name    : TemperleyLieb.Gram.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:34.24876+00:00
-- url     : https://prove2.me/theorems/865c2940-bb34-41b2-adeb-fba6f84920b3
-- title:
--   Lemma 2.3, p. 3 — Murphy cellular basis
-- statement:
--   For every positive integer $n$, the elements $m_{uv}=v_u^*m_\lambda v_v$, indexed by pairs of standard tableaux of a common shape $\lambda$, form a cellular basis of $A_n(x)$ over $R=\mathbb Z[x]$. Its algebra anti-involution interchanges the two tableaux and fixes each generator:
--
--   $$m_{uv}^*=m_{vu},\qquad e_i^*=e_i\quad(1\le i<n).$$
--
--   The cellular-basis condition also includes the right multiplication congruence of Eq. (2.2), with coefficients independent of the row tableau. This supplies the actual Gram form used by the later statements.
--
--   **Formalization Note** The published `CellDatum` definition contains the basis, anti-involution and multiplication congruence. Existence is asserted, so later uses of such a datum are not vacuous. The $m_\lambda$ endpoint is corrected as disclosed in the definitions item.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 3, Lemma 2.3, Eqs. (2.1)–(2.2)

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram

/-- Enyang, Lemma 2.3, p. 3: the displayed Murphy elements form a cellular basis,
and its anti-involution fixes the Temperley–Lieb generators. -/
theorem lemma_2_3 (n : ℕ) (hn : 1 ≤ n) :
    ∃ D : RDatum n,
      IsMurphyDatum R Polynomial.X n D ∧
      ∀ i : ℕ, 1 ≤ i → i < n → D.star (e R Polynomial.X n i) = e R Polynomial.X n i := by sorry

end TemperleyLieb.Gram
