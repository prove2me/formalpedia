-- Prove2me | Theorems.Thm_Rank2Sha_curve389a1_finite_sha
-- name    : Rank2Sha.curve389a1_finite_sha
-- status  : Open
-- author  : @barindersbanwait
-- created : 2026-11-25T11:56:04.608309+00:00
-- url     : https://prove2.me/theorems/969457db-f9ab-5e58-82b9-2f51c8173c1c
-- title:
--   The curve 389a1 has rank at least $2$ and finite Shafarevich–Tate group
-- statement:
--   Let $E$ be the elliptic curve over $\mathbb{Q}$ given by
--
--   $$
--   E : \; y^2 + y = x^3 + x^2 - 2x ,
--   $$
--
--   which has LMFDB label 389.a1. The statement has two parts.
--
--   1. The Mordell–Weil group $E(\mathbb{Q})$ has rank at least $2$.
--   2. The Shafarevich–Tate group $\text{Ш}(E/\mathbb{Q})$ is finite.
--
--   Together:
--
--   $$
--   \operatorname{rank} E(\mathbb{Q}) \ge 2 \quad\text{and}\quad \#\text{Ш}(E/\mathbb{Q}) < \infty .
--   $$
--
--   Finiteness of $\text{Ш}(E/\mathbb{Q})$ is conjectured for every elliptic curve. It is a theorem when the $L$-function of $E$ vanishes to order at most $1$ at $s = 1$, and such curves have rank at most $1$. It is not known for any elliptic curve over $\mathbb{Q}$ of rank at least $2$. This statement would be the first such case.
--
--   **Formalization Note** The rank is `Module.finrank ℤ E.Point`, which is $0$ when the rank is infinite, so the first part also asserts that the rank is finite. The group $\text{Ш}(E/\mathbb{Q})$ is `E.tateShafarevich` of the definition `Rank2Sha_TateShafarevich`: the classes in $H^1(G_{\mathbb{Q}}, E(\overline{\mathbb{Q}}))$ that restrict to zero in $H^1(G_{\mathbb{Q}_v}, E(\overline{\mathbb{Q}}))$ for every place $v$ of $\mathbb{Q}$.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Graduate Texts in Mathematics 106, Springer 2009, https://doi.org/10.1007/978-0-387-09494-6, Chapter X, Section 4 (conjectured finiteness of the Shafarevich-Tate group) ; W. Stein and C. Wuthrich, Algorithms for the arithmetic of elliptic curves using Iwasawa theory, Math. Comp. 82 (2013), 1757-1792, https://doi.org/10.1090/S0025-5718-2012-02649-4, Section 1.1: "The group Ш(E/Q) is not known to be finite for even a single elliptic curve with r_an ≥ 2." ; https://www.lmfdb.org/EllipticCurve/Q/389/a/1

import Mathlib
import Definitions.Def_Rank2Sha_Curves
import Definitions.Def_Rank2Sha_TateShafarevich

namespace Rank2Sha
theorem curve389a1_finite_sha :
    2 ≤ Module.finrank ℤ curve389a1.Point ∧ Finite curve389a1.tateShafarevich := by sorry
end Rank2Sha
