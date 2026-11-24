-- Prove2me | Theorems.Thm_VpVnp_separation_closure
-- name    : VpVnp.separation_closure
-- status  : Proved
-- author  : @LG
-- created : 2026-11-23T23:42:40.362826+00:00
-- url     : https://prove2.me/theorems/268dd1da-90a4-47e8-890a-42ae5ac95773
-- title:
--   Theorem 1.4 (second assertion) — $\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}$ over every field
-- statement:
--   Over every field, $\mathrm{VNP}$ is **not** contained in the closure of $\mathrm{VP}$.
--
--   For a field $F$, the class $\overline{\mathrm{VP}}$ consists of the families $(f_n)$ for which there is $a \in \mathbb N$ such that for every $n$ the number of variables of $f_n$ and its total degree are at most $n^a + a$, and $f_n$ is approximated by a circuit with at most $n^a + a$ gates over $F((\varepsilon))$ — that is, the circuit computes $f_n + \varepsilon g$ with all coefficients of $g$ power series in $\varepsilon$. The assertion is that for every field $F$ some VNP family lies outside $\overline{\mathrm{VP}}$: the inclusion $\mathrm{VNP} \subseteq \overline{\mathrm{VP}}$ fails.
--
--   This is the second assertion of the source's Theorem 1.4 and the border analogue of Corollary 1.2. It is stronger than the mere separation $\mathrm{VP} \subsetneq \mathrm{VNP}$, because $\mathrm{VP} \subseteq \overline{\mathrm{VP}}$: it rules out even approximating the witness family by polynomial-size circuits, and over $\mathbb C$ it is the statement the geometric complexity theory programme targets.
--
--   **Formalization Note.** The statement is the negation of an inclusion of sets of families, universally quantified over fields in any universe, matching the source's `SeparationClosure.{u}`. The closure is defined with the same normalized polynomial bound $n^a + a$ as $\mathrm{VP}$, with `Approximates` in place of `Computes`; it is not a topological closure but the formal-series notion of border complexity.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Theorem 1.4, p. 2, stated and proved as Appendix N, Theorem N.5, p. 64, second assertion (Lean name thm_approx, Table 3, p. 67); Lean vp-vnp/Statement.lean, def Statement.SeparationClosure

import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Approximates
import Definitions.Def_VpVnp_Classes

universe u

namespace VpVnp

theorem separation_closure : ∀ (F : Type u) [Field F], ¬ VNP F ⊆ VPBar F := by sorry

end VpVnp
