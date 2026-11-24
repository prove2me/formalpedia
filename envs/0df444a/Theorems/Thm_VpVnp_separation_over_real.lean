-- Prove2me | Theorems.Thm_VpVnp_separation_over_real
-- name    : VpVnp.separation_over_real
-- status  : Proved
-- author  : @LG
-- created : 2026-11-23T23:39:25.552177+00:00
-- url     : https://prove2.me/theorems/b3ba7dcd-8500-43e7-aefc-c39b92977d47
-- title:
--   Corollary L.3 — $\mathrm{VP} \subsetneq \mathrm{VNP}$ over $\mathbb R$
-- statement:
--   Valiant's conjecture over the real numbers: $\mathrm{VP}$ is a **proper** subset of $\mathrm{VNP}$.
--
--   Here a family is a sequence $(f_n)$ of polynomials over $\mathbb R$, with $f_n$ in finitely many variables. The family lies in $\mathrm{VP}$ if for some $a \in \mathbb N$ and every $n$ the number of variables of $f_n$, its total degree and its circuit size are all at most $n^a + a$; it lies in $\mathrm{VNP}$ if $f_n(x) = \sum_{e \in \{0,1\}^{r(n)}} g_n(x,e)$ identically as polynomials, for some function $r$ and some family $(g_n)$ in $\mathrm{VP}$ with $r(n)$ additional Boolean variables. The inclusion $\mathrm{VP} \subseteq \mathrm{VNP}$ holds for every field; the assertion here is that over $\mathbb R$ it is strict, i.e. some VNP family has no polynomial-size circuits.
--
--   This is the real-number case of the source's Corollary 1.2 and the class-level form of Theorem L.1: the permanent family lies in VNP, and the lower bound excludes it from VP.
--
--   **Formalization Note.** The statement is a strict inclusion of sets of families (`⊂`), which packages both the inclusion and the existence of a witness outside $\mathrm{VP}$. The polynomial bound is normalized to $n^a + a$, and the gate count includes variables and constants.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Appendix L, Corollary L.3, p. 59 (Lean name cor_classes, Table 3, p. 67)

import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Approximates
import Definitions.Def_VpVnp_Classes

universe u

namespace VpVnp

theorem separation_over_real : VP ℝ ⊂ VNP ℝ := by sorry

end VpVnp
