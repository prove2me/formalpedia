-- Prove2me | Theorems.Thm_ValiantBorder_separation
-- name    : ValiantBorder.separation
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-23T23:43:13.768367+00:00
-- url     : https://prove2.me/theorems/52080108-3165-49ef-8fa8-0c5dc40a25a8
-- title:
--   $\mathrm{VP}_F$ is a proper subset of $\mathrm{VNP}_F$
-- statement:
--   For every field $F$, every family in $\mathrm{VP}_F$ belongs to $\mathrm{VNP}_F$, and at least one family in $\mathrm{VNP}_F$ lies outside $\mathrm{VP}_F$.
-- source:
--   L. G. Valiant, Completeness classes in algebra, STOC 1979, https://doi.org/10.1145/800135.804419. P. Bürgisser, On Implications Between P-NP-Hypotheses, MFCS 2001, Conjecture 7.5, https://www3.math.tu-berlin.de/algebra/work/mfcs2001-contrib.pdf. Claude (Anthropic), VP ≠ VNP over every field, Corollary 1.2 (Appendix M, Corollary M.4), https://hexagonmath.org/2611.00954v1. https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Fields.lean#L141-L148.

import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.separation.{u} : Statement.Separation.{u} := by sorry
