-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P72_finiteModulationVarianceCriteria
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P72.finiteModulationVarianceCriteria
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T07:43:58.265772+00:00
-- url     : https://prove2.me/theorems/0bc11ab5-5edf-4853-8fbb-772e964839ed
-- title:
--   Finite-modulation asymmetric variance criteria
-- statement:
--   Let $V\ge1$, $N_0>0$, $G_x,G_p>0$, $\chi_x,\chi_p\ge0$, and $1/V\le s\le V$. Write $A_q=G_q(\chi_q+s)N_0$ for the explicit Alice variance expression and $E_x=N_0/[G_p(\chi_p+1/V)]$, $E_p=N_0/[G_x(\chi_x+1/V)]$ for the crossed Eve expressions assumed attained in (38)–(39). Then
--
--   $$
--   \begin{aligned}
--   E_x>A_x&\iff (G_x\chi_x+G_xs)(G_p\chi_p+G_p/V)<1,\\
--   E_p>A_p&\iff (G_p\chi_p+G_ps)(G_x\chi_x+G_x/V)<1.
--   \end{aligned}
--   $$
--
--   Consequently the disjunction of variance advantages is equivalent to the disjunction of these product inequalities. Under $G_x=G_p=G$ and $\chi_x=\chi_p=\chi$, it reduces to $(G\chi+Gs)(G\chi+G/V)<1$.
--
--   This result is the exact algebraic comparison of the source's explicit variance expressions. The interpretation as uniform operational security is deferred under the paper seed.
-- source:
--   Reverse reconciliation protocols for quantum cryptography with continuous variables, arXiv:quant-ph/0204127v1, PDF p. 4, III.A, (38)–(44): finite-modulation variance advantage criteria

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P72

/-- Grosshans--Grangier, PDF p.4, III.A, (38)--(44).
These are the exact algebraic variance comparisons, retaining the asymmetric
OR and the crossed quadrature indices. The source's operational interpretation
is deferred under the original paper seed. -/
theorem finiteModulationVarianceCriteria
    (V N0 Gx Gp chix chip s : ℝ)
    (hV : 1 ≤ V) (hN0 : 0 < N0) (hGx : 0 < Gx) (hGp : 0 < Gp)
    (hchix : 0 ≤ chix) (hchip : 0 ≤ chip)
    (hslo : 1 / V ≤ s) (hshi : s ≤ V) :
    (eveVarianceExpression Gp chip V N0 > aliceVarianceExpression Gx chix s N0 ↔
      (Gx * chix + Gx * s) * (Gp * chip + Gp / V) < 1) ∧
    (eveVarianceExpression Gx chix V N0 > aliceVarianceExpression Gp chip s N0 ↔
      (Gp * chip + Gp * s) * (Gx * chix + Gx / V) < 1) ∧
    ((eveVarianceExpression Gp chip V N0 > aliceVarianceExpression Gx chix s N0 ∨
      eveVarianceExpression Gx chix V N0 > aliceVarianceExpression Gp chip s N0) ↔
      ((Gx * chix + Gx * s) * (Gp * chip + Gp / V) < 1 ∨
       (Gp * chip + Gp * s) * (Gx * chix + Gx / V) < 1)) ∧
    (Gx = Gp → chix = chip →
      ((eveVarianceExpression Gp chip V N0 > aliceVarianceExpression Gx chix s N0 ∨
        eveVarianceExpression Gx chix V N0 > aliceVarianceExpression Gp chip s N0) ↔
        varianceProduct Gx chix V s < 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P72

end
