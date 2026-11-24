-- Prove2me | Theorems.Thm_VpVnp_separation
-- name    : VpVnp.separation
-- status  : Proved
-- author  : @LG
-- created : 2026-11-23T23:41:05.746178+00:00
-- url     : https://prove2.me/theorems/9db57fbe-a3ba-408b-8370-9ff0d6b77299
-- title:
--   Corollary 1.2 — $\mathrm{VP} \subsetneq \mathrm{VNP}$ over every field
-- statement:
--   Valiant's conjecture over every field: for every field $F$, the class $\mathrm{VP}$ is a **proper** subset of $\mathrm{VNP}$.
--
--   A family over $F$ is a sequence $(f_n)$ of polynomials, $f_n$ in finitely many variables. It lies in $\mathrm{VP}$ if for some $a \in \mathbb N$ and every $n$ the number of variables of $f_n$, its total degree and its arithmetic-circuit size are all at most $n^a + a$, where variables and constants count as gates. It lies in $\mathrm{VNP}$ if $f_n(x) = \sum_{e \in \{0,1\}^{r(n)}} g_n(x,e)$ identically as polynomials, for some function $r : \mathbb N \to \mathbb N$ and some family $(g_n)$ in $\mathrm{VP}$ with $r(n)$ additional Boolean variables. The inclusion $\mathrm{VP} \subseteq \mathrm{VNP}$ is automatic; the content is that it is strict over every field, including finite fields and fields of positive characteristic.
--
--   This is the class-level consequence of the mission's goal: the Hamiltonian cycle family lies in VNP over every field, and the goal's lower bound excludes it from VP. It is the algebraic analogue of $\mathrm{P} \neq \mathrm{NP}$, and does not imply it.
--
--   **Formalization Note.** The statement is universally quantified over fields in any universe, matching the source's `Separation.{u}`. Strict inclusion of sets of families (`⊂`) packages the inclusion together with the existence of a family in $\mathrm{VNP} \setminus \mathrm{VP}$. The classes are defined over commutative semirings in the definition layer, as the source's Appendix Q records, while this statement is over fields.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Corollary 1.2, p. 2, stated and proved as Appendix M, Corollary M.4, p. 62 (Lean name cor_allclasses, Table 3, p. 67); Lean vp-vnp/Statement.lean, def Statement.Separation

import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Approximates
import Definitions.Def_VpVnp_Classes

universe u

namespace VpVnp

theorem separation : ∀ (F : Type u) [Field F], VP F ⊂ VNP F := by sorry

end VpVnp
