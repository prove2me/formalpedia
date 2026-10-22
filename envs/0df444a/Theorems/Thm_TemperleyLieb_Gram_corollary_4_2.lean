-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_corollary_4_2
-- name    : TemperleyLieb.Gram.corollary_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:35.184388+00:00
-- url     : https://prove2.me/theorems/ea87a1cd-60e8-42ca-9276-e3e31725ec8f
-- title:
--   Corollary 4.2, p. 16 — alternative recursion for the Jucys–Murphy elements
-- statement:
--   In the Temperley–Lieb algebra $A_n(x)$ over $R=\mathbb Z[x]$, with $T_i$, $z_i$ as on p. 10 and $p_i$ as on p. 13, for $i\ge 2$,
--
--   $$T_{i+1}=-e_iT_i-T_ie_i+(p_i-xz_{i-1})e_i-z_{i-1}.$$
--
--   This recursion replaces the term $e_ie_{i-1}T_ie_i$ of the defining recursion by an expression in $e_i$ and the central element $z_{i-1}$, and is the form used to compute the action of the generators on the seminormal basis.
--
--   **Formalization Note** The identity is stated for $2\le i\le n-1$, the range in which $e_i$ is a generator of $A_n(x)$ and $T_{i+1}$ is the element of the paper. The scalar $p_i$ enters through the algebra map $R\to A_n(x)$.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 16, Corollary 4.2

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram

/-- Enyang, Corollary 4.2, p. 16: the alternative recursion for the
Jucys–Murphy elements, for the indices `2 ≤ i ≤ n - 1` whose generators exist. -/
theorem corollary_4_2 (n i : ℕ) (hi : 2 ≤ i) (hin : i + 1 ≤ n) :
    JM R Polynomial.X n (i + 1) =
      -(e R Polynomial.X n i * JM R Polynomial.X n i) -
        JM R Polynomial.X n i * e R Polynomial.X n i +
        (algebraMap R (TL R Polynomial.X n) (p i) -
            (Polynomial.X : R) • zJM R Polynomial.X n (i - 1)) * e R Polynomial.X n i -
        zJM R Polynomial.X n (i - 1) := by sorry

end TemperleyLieb.Gram
