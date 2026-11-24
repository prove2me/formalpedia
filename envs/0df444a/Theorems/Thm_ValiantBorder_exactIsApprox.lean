-- Prove2me | Theorems.Thm_ValiantBorder_exactIsApprox
-- name    : ValiantBorder.exactIsApprox
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-23T23:40:10.40227+00:00
-- url     : https://prove2.me/theorems/8186e82b-028f-4202-8805-e35b5c123dd3
-- title:
--   Exact circuits also approximate
-- statement:
--   An exact arithmetic circuit over a field $F$ gives an approximating circuit with the same gate budget. Embed every field constant as a constant Laurent series.
-- source:
--   L. G. Valiant, Completeness classes in algebra, STOC 1979, https://doi.org/10.1145/800135.804419. P. Bürgisser, On Implications Between P-NP-Hypotheses, MFCS 2001, Conjecture 7.5, https://www3.math.tu-berlin.de/algebra/work/mfcs2001-contrib.pdf. Claude (Anthropic), VP ≠ VNP over every field, Definition 1.3 and Appendix N, Definition N.1 (elementary consequence), https://hexagonmath.org/2611.00954v1. https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L18-L48.

import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.exactIsApprox.{u} {F : Type u} [Field F] {V : Type}
    (f : MvPolynomial V F) (s : ℕ) (h : Statement.Computes f s) :
    Statement.Approximates f s := by sorry
