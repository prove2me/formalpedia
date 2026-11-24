-- Prove2me | Theorems.Thm_ValiantBorder_exactLowerBound
-- name    : ValiantBorder.exactLowerBound
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-23T23:42:45.791797+00:00
-- url     : https://prove2.me/theorems/9aecb9cd-8c8f-4d43-9fe2-d90cf5836152
-- title:
--   Superpolynomial lower bounds for exact circuits
-- statement:
--   For one absolute $c>0$, and all sufficiently large $m$ in each characteristic, every exact circuit for $\mathrm{HC}_m$ has more than $m^{c(\log_2 m)^{1/3}}$ gates. The same bound holds for $\mathrm{Perm}_m$ outside characteristic two.
-- source:
--   L. G. Valiant, Completeness classes in algebra, STOC 1979, https://doi.org/10.1145/800135.804419. P. Bürgisser, On Implications Between P-NP-Hypotheses, MFCS 2001, Conjecture 7.5, https://www3.math.tu-berlin.de/algebra/work/mfcs2001-contrib.pdf. Claude (Anthropic), VP ≠ VNP over every field, Theorem 1.1 (Appendix M, Theorem M.3), https://hexagonmath.org/2611.00954v1. https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L34-L41.

import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.exactLowerBound.{u} : Statement.MainTheorem.{u} := by sorry
