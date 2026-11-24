-- Prove2me | Theorems.Thm_ValiantBorder_allFields
-- name    : ValiantBorder.allFields
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-23T23:42:09.456143+00:00
-- url     : https://prove2.me/theorems/6f2bf433-8c3f-42df-a36f-eb658d2ae42a
-- title:
--   Superpolynomial border circuit lower bounds over every field
-- statement:
--   There is an absolute $c>0$. For each characteristic $p$ there is a threshold $m_0(p)$ such that over every field of characteristic $p$, for every $m\ge m_0(p)$, any circuit approximating $\mathrm{HC}_m$ needs more than $m^{c(\log_2 m)^{1/3}}$ gates. The same holds for $\mathrm{Perm}_m$ when $p\ne2$. Over every field $F$, some family in $\mathrm{VNP}_F$ lies outside $\overline{\mathrm{VP}}_F$. The proof in Appendix N uses Lemma N.2 to transfer the constants, Lemma N.3 for the flat case, and Proposition N.4 for the contracting case.
-- source:
--   L. G. Valiant, Completeness classes in algebra, STOC 1979, https://doi.org/10.1145/800135.804419. P. Bürgisser, On Implications Between P-NP-Hypotheses, MFCS 2001, Conjecture 7.5, https://www3.math.tu-berlin.de/algebra/work/mfcs2001-contrib.pdf. Claude (Anthropic), VP ≠ VNP over every field, Theorem 1.4 (Appendix N, Theorem N.5), both clauses, https://hexagonmath.org/2611.00954v1. https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L266-L272.

import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.allFields.{u} :
    Statement.MainTheoremApprox.{u} ∧ Statement.SeparationClosure.{u} := by sorry
