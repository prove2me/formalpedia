-- Prove2me | Theorems.Thm_SemialgebraicSDP_Psatz_monomial_vector_card
-- name    : SemialgebraicSDP.Psatz.monomial_vector_card
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:22.726974+00:00
-- url     : https://prove2.me/theorems/80782501-cb05-40e9-b387-818ae567d102
-- title:
--   §3.2 — the vector $z$ of monomials of degree $\le d$ has length $\binom{n+d}{d}$
-- statement:
--   Let $n,d\in\mathbb N$ and let $z$ be the vector of all monomials $x^\alpha$ in $n$ variables of total degree at most $d$, as in (3.5). Then the length of $z$ is
--   $$
--   |\{\alpha\in\mathbb N^n : \alpha_1+\dots+\alpha_n\le d\}|=\binom{n+d}{d}.
--   $$
--   This fixes the size of the Gram matrices in the semidefinite programs of Theorem 3.3 and Theorem 5.1.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 298, §3.2, sentence after (3.5)

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

namespace SemialgebraicSDP.Psatz

open MvPolynomial

theorem monomial_vector_card (n d : ℕ) :
    Fintype.card (Mon n d) = (n + d).choose d := by sorry

end SemialgebraicSDP.Psatz
