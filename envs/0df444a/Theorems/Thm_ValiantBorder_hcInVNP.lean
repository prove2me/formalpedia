-- Prove2me | Theorems.Thm_ValiantBorder_hcInVNP
-- name    : ValiantBorder.hcInVNP
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-23T23:41:30.603819+00:00
-- url     : https://prove2.me/theorems/2e7f56ca-b65a-42c6-ba67-b898e09c4094
-- title:
--   The Hamiltonian cycle family belongs to $\mathrm{VNP}$
-- statement:
--   Over each field $F$, the Hamiltonian cycle polynomials on $n$ labeled vertices form a family in $\mathrm{VNP}_F$. The monomials correspond to permutations consisting of one cycle through all vertices.
-- source:
--   L. G. Valiant, Completeness classes in algebra, STOC 1979, https://doi.org/10.1145/800135.804419. P. Bürgisser, On Implications Between P-NP-Hypotheses, MFCS 2001, Conjecture 7.5, https://www3.math.tu-berlin.de/algebra/work/mfcs2001-contrib.pdf. Claude (Anthropic), VP ≠ VNP over every field, §1.1 and Appendix M, proof of Corollary M.4, https://hexagonmath.org/2611.00954v1. https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Fields.lean#L130-L142.

import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.hcInVNP.{u} (F : Type u) [Field F] :
    ({ vars := fun n => Fin n × Fin n, poly := Statement.hc F } : Statement.Family F)
      ∈ Statement.VNP F := by sorry
