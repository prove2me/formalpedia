-- Prove2me | Theorems.Thm_Rank2Sha_curve389a1_sha_no_p_torsion_almost_all
-- name    : Rank2Sha.curve389a1_sha_no_p_torsion_almost_all
-- status  : Open
-- author  : @barindersbanwait
-- created : 2026-11-25T11:45:45.271445+00:00
-- url     : https://prove2.me/theorems/89a3f82d-e84a-5096-bf1f-e59c7b084bed
-- title:
--   $\text{Ш}(E/\mathbb{Q})[p] = 0$ for all but finitely many $p$, for 389a1
-- statement:
--   Let $E$ be the elliptic curve over $\mathbb{Q}$ given by
--
--   $$
--   E : \; y^2 + y = x^3 + x^2 - 2x ,
--   $$
--
--   which has LMFDB label 389.a1, and let $\text{Ш}(E/\mathbb{Q})$ be its Shafarevich–Tate group. There is a finite set $S$ of prime numbers such that for every prime $p \notin S$ the group $\text{Ш}(E/\mathbb{Q})$ has no element of order $p$:
--
--   $$
--   \exists\, S \text{ finite}, \quad \forall\, p \notin S \text{ prime}, \quad \text{Ш}(E/\mathbb{Q})[p] = 0 .
--   $$
--
--   This is the part of the finiteness of $\text{Ш}(E/\mathbb{Q})$ for which no method is known when the rank is at least $2$. Every published criterion verifies $\text{Ш}(E/\mathbb{Q})[p] = 0$ at one prime $p$ at a time, by a computation that depends on $p$. The statement asks for all but finitely many primes at once.
--
--   **Formalization Note** The group $\text{Ш}(E/\mathbb{Q})$ is `E.tateShafarevich` of the definition `Rank2Sha_TateShafarevich`: the classes in $H^1(G_{\mathbb{Q}}, E(\overline{\mathbb{Q}}))$, continuous cohomology with $E(\overline{\mathbb{Q}})$ discrete, whose restriction to $H^1(G_{\mathbb{Q}_v}, E(\overline{\mathbb{Q}}))$ is zero for every place $v$ of $\mathbb{Q}$, finite and infinite. The set $S$ is a finite set of natural numbers; its non-prime members play no role.
-- source:
--   W. Stein and C. Wuthrich, Algorithms for the arithmetic of elliptic curves using Iwasawa theory, Math. Comp. 82 (2013), 1757-1792, https://doi.org/10.1090/S0025-5718-2012-02649-4, Section 1.1 (open status in rank at least 2) and Theorem 12.3 (Sha(389a/Q)[p] = 0 for p = 2 and all good ordinary p < 48,859 except 16,231; numbering of the authors' preprint) ; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Graduate Texts in Mathematics 106, Springer 2009, https://doi.org/10.1007/978-0-387-09494-6, Chapter X, Section 4

import Mathlib
import Definitions.Def_Rank2Sha_Curves
import Definitions.Def_Rank2Sha_TateShafarevich

namespace Rank2Sha
theorem curve389a1_sha_no_p_torsion_almost_all :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ x : curve389a1.tateShafarevich, p • x = 0 → x = 0 := by sorry
end Rank2Sha
