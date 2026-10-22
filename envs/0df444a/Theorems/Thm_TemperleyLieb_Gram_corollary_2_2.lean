-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_corollary_2_2
-- name    : TemperleyLieb.Gram.corollary_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:29.204503+00:00
-- url     : https://prove2.me/theorems/53c1041a-7ebe-4ab3-b584-0e863b485180
-- title:
--   Corollary 2.2, p. 3 — neighbouring tableaux differ by a factor e_{k−1}
-- statement:
--   Let $A_n(x)$ be the Temperley–Lieb algebra over $R=\mathbb Z[x]$ with generators $e_1,\dots,e_{n-1}$, and let $\lambda=(f,n-2f)$ be a partition of $n$. For an up–down tableau $\mathfrak t\in\mathfrak T_n(\lambda)$ write $\operatorname{Shape}(\mathfrak t|_i)$ for its shape at stage $i$, and $v_{\mathfrak t}\in A_n(x)$ for the element defined recursively on p. 2.
--
--   Let $1<k<n$ and let $\mathfrak s\ne\mathfrak t$ be tableaux in $\mathfrak T_n(\lambda)$ with $\operatorname{Shape}(\mathfrak s|_i)=\operatorname{Shape}(\mathfrak t|_i)$ for every $i\in\{0,1,\dots,n\}\setminus\{k-1\}$. Then
--
--   $$\operatorname{Shape}(\mathfrak s|_{k-1})=(j-1,k-2j+1)\ \text{ and }\ \operatorname{Shape}(\mathfrak t|_{k-1})=(j,k-2j-1)\quad\text{for some } j\ \iff\ v_{\mathfrak s}=v_{\mathfrak t}\,e_{k-1}.$$
--
--   The criterion identifies the pairs of tableaux that the generator $e_{k-1}$ links in the cell module; it is used in the computation of the action of the generators on the seminormal basis.
--
--   **Formalization Note** A tableau is its cup-count path, and `cups s i` is the number of cups of $\operatorname{Shape}(\mathfrak s|_i)$, so the shape condition reads `cups s (k-1) + 1 = j` and `cups t (k-1) = j` with $j\ge1$. The integer $j$, unnamed on the page, is necessarily the common number of cups at stage $k$.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 3, Corollary 2.2; p. 2, definition of v_t

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram

/-- Enyang, Corollary 2.2, p. 3: two up–down tableaux of the same shape that differ
only at stage `k - 1` differ by a right factor `e_{k-1}` in their `v` elements,
exactly when the first has one cup fewer at stage `k - 1`. -/
theorem corollary_2_2 (n : ℕ) (f : Fin (n / 2 + 1)) (k : ℕ) (hk1 : 1 < k) (hkn : k < n)
    (s t : Tab n f) (hst : s ≠ t)
    (hagree : ∀ i : ℕ, i ≤ n → i ≠ k - 1 → cups s i = cups t i) :
    (∃ j : ℕ, 1 ≤ j ∧ cups s (k - 1) + 1 = j ∧ cups t (k - 1) = j) ↔
      vElt R Polynomial.X s = vElt R Polynomial.X t * e R Polynomial.X n (k - 1) := by sorry

end TemperleyLieb.Gram
