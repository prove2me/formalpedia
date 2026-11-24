-- Prove2me | Theorems.Thm_ValiantBorder_borderDetToCircuit
-- name    : ValiantBorder.borderDetToCircuit
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-23T23:43:50.423799+00:00
-- url     : https://prove2.me/theorems/61e8b253-994f-4248-8510-f8528673ce4f
-- title:
--   From a limit of padded determinants to an approximating circuit
-- statement:
--   There is a fixed natural exponent $a$ such that if the padded complex permanent of size $m$ is a coefficientwise limit of size-$n$ determinants of homogeneous linear forms, with $m\le n$, then the unpadded permanent has a Laurent-series approximating circuit with at most $(m+n+2)^a$ gates.
-- source:
--   L. G. Valiant, Completeness classes in algebra, STOC 1979, https://doi.org/10.1145/800135.804419. P. Bürgisser, On Implications Between P-NP-Hypotheses, MFCS 2001, Conjecture 7.5, https://www3.math.tu-berlin.de/algebra/work/mfcs2001-contrib.pdf. Claude (Anthropic), VP ≠ VNP over every field, Appendix N, Remark N.6 (comparison needed for the platform formulation, proposed here), https://hexagonmath.org/2611.00954v1. https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L43-L52. K. Mulmuley and M. Sohoni, Geometric Complexity Theory I, https://doi.org/10.1137/S009753970038715X. Platform target https://prove2.me/theorems/498980f7-6512-4a79-9796-68140c55c691. Laurent parameter selection: Guo, Saxena and Sinhababu, CCC 2018, Theorem 15, https://doi.org/10.4230/LIPIcs.CCC.2018.10.

import Definitions.Def_VP_VNP_all_fields
import Definitions.Def_GCT_determinantal_complexity

theorem ValiantBorder.borderDetToCircuit :
    ∃ a : ℕ, ∀ m n : ℕ, m ≤ n →
      GCT.HasBorderLinearDetRep n (GCT.paddedPerm m n) →
      Statement.Approximates (Statement.perm ℂ m) ((m + n + 2) ^ a) := by sorry
