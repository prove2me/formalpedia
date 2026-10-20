-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_classicalCorrelation_converse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.classicalCorrelation_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:01:25.937249+00:00
-- url     : https://prove2.me/theorems/68a46341-da34-49c7-9ef0-dafb2f32a71b
-- title:
--   Proposition 19
-- statement:
--   Let $N:A\to B$ be CPTP, with $R,A,B$ of common positive dimension $d$, and let $\Phi_c=d^{-1}\sum_i|ii\rangle\langle ii|$. Suppose $0\le\varepsilon<1$ and $\frac12\|(\operatorname{id}\otimes N)(\Phi_c)-\Phi_c\|_1\le\varepsilon$. In each infimum below, $M:A\to B$ ranges over every CP map with $\beta(M)\le1$. The entropy $D_H^\varepsilon$ is the hypothesis-testing relative entropy, and $\widehat D_\alpha$ is geometric Rényi relative entropy. In the formula, $N(\Phi_c)$ and $M(\Phi_c)$ mean that the identity acts on the reference register.
--
--   $$
--   \log_2 d\le\inf_M D_H^\varepsilon(N(\Phi_c)\Vert M(\Phi_c)),\qquad\log_2 d\le\inf_M\widehat D_\alpha(N(\Phi_c)\Vert M(\Phi_c))+\frac\alpha{\alpha-1}\log_2\frac1{1-\varepsilon}\quad(1<\alpha\le2).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 11, Proposition 19

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 19, arXiv:2010.01058v3, PDF pp.11,12.
 -/
theorem classicalCorrelation_converse {I : Type} [Fintype I] [Nonempty I]
    (N : Superop I I) (hN : IsChannel N) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon ∧ epsilon < 1)
    (herror : traceNorm (idTensorSuperop N (classicalPhi I) - classicalPhi I) / 2 ≤ epsilon) :
    (Real.logb 2 (Fintype.card I) : EReal) ≤ pointPhiInf (testingD epsilon) N ∧
      ∀ alpha : ℝ, 1 < alpha → alpha ≤ 2 →
        (Real.logb 2 (Fintype.card I) : EReal) ≤
          pointPhiInf (geometricD alpha) N + penalty alpha epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
