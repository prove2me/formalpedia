-- Prove2me | Theorems.Thm_Rank2Sha_curve389a1_sha_primary_finite
-- name    : Rank2Sha.curve389a1_sha_primary_finite
-- status  : Open
-- author  : @barindersbanwait
-- created : 2026-11-25T11:51:22.968793+00:00
-- url     : https://prove2.me/theorems/03038b0b-2585-5eaa-bd09-1953cd73ddc4
-- title:
--   $\text{Ш}(E/\mathbb{Q})[p^\infty]$ is finite for every prime $p$, for 389a1
-- statement:
--   Let $E$ be the elliptic curve over $\mathbb{Q}$ given by
--
--   $$
--   E : \; y^2 + y = x^3 + x^2 - 2x ,
--   $$
--
--   which has LMFDB label 389.a1, and let $p$ be a prime number. The $p$-primary part of the Shafarevich–Tate group of $E$,
--
--   $$
--   \text{Ш}(E/\mathbb{Q})[p^\infty] = \{\, x \in \text{Ш}(E/\mathbb{Q}) : p^n x = 0 \text{ for some } n \ge 0 \,\} ,
--   $$
--
--   is finite.
--
--   The group $\text{Ш}(E/\mathbb{Q})[p^\infty]$ is the sum of a finite group and finitely many copies of $\mathbb{Q}_p/\mathbb{Z}_p$, so the statement says that it has no divisible part. For a given prime $p$ this can be verified by a computation at $p$ in many cases; the statement is for every prime.
--
--   **Formalization Note** The group $\text{Ш}(E/\mathbb{Q})$ is `E.tateShafarevich` of the definition `Rank2Sha_TateShafarevich`: the classes in $H^1(G_{\mathbb{Q}}, E(\overline{\mathbb{Q}}))$, continuous cohomology with $E(\overline{\mathbb{Q}})$ discrete, whose restriction to $H^1(G_{\mathbb{Q}_v}, E(\overline{\mathbb{Q}}))$ is zero for every place $v$ of $\mathbb{Q}$, finite and infinite.
-- source:
--   W. Stein and C. Wuthrich, Algorithms for the arithmetic of elliptic curves using Iwasawa theory, Math. Comp. 82 (2013), 1757-1792, https://doi.org/10.1090/S0025-5718-2012-02649-4, Theorem 12.3 (numbering of the authors' preprint) ; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Graduate Texts in Mathematics 106, Springer 2009, https://doi.org/10.1007/978-0-387-09494-6, Chapter X, Section 4

import Mathlib
import Definitions.Def_Rank2Sha_Curves
import Definitions.Def_Rank2Sha_TateShafarevich

namespace Rank2Sha
theorem curve389a1_sha_primary_finite (p : ℕ) (hp : p.Prime) :
    {x : curve389a1.tateShafarevich | ∃ n : ℕ, p ^ n • x = 0}.Finite := by sorry
end Rank2Sha
