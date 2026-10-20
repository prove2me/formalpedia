-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_hermitianAlternative_essential
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.hermitianAlternative_essential
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:42:21.142187+00:00
-- url     : https://prove2.me/theorems/967d72c1-e1a0-4dc2-a8fc-f8c218780247
-- title:
--   Hermitian alternatives strictly improve the testing optimization
-- statement:
--   For $\theta\in[\pi/12,\pi/6]$, let $\phi_\theta=\cos\theta|00\rangle+\sin\theta|11\rangle$ and $\rho_\theta=\tfrac34|\phi_\theta\rangle\langle\phi_\theta|+\tfrac14|10\rangle\langle10|$. Put $\varepsilon=1-\sqrt3/2$. There exists such a $\theta$ for which
--
--   $$\inf_{G=G^\dagger,\,\|G^{T_B}\|_1\le1}D_H^\varepsilon(\rho_\theta\|G)<\inf_{G\ge0,\,\|G^{T_B}\|_1\le1}D_H^\varepsilon(\rho_\theta\|G).$$
--
--   Here $T_B$ transposes Bob, the trace norm is the Schatten one-norm, and $D_H^\varepsilon$ is minus the base-two logarithm of the minimum $\operatorname{Tr}(MG)$ over effects accepting $\rho_\theta$ with probability at least $1-\varepsilon$, with value $+\infty$ when that minimum is nonpositive. The source supports this strict separation numerically; no analytical certificate or exact numerical gap is claimed. This explains why positivity cannot replace Hermiticity in the exact characterization.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 17, Appendix A: Hermitian alternatives cannot be restricted to positive operators

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Appendix A, arXiv:1706.06221v3, PDF pp.17–18, Eqs.(65)–(68), Figure 4.
Existential strict separation is supported there numerically; no exact plotted gap is asserted. -/
theorem hermitianAlternative_essential :
    ∃ theta : ℝ, Real.pi / 12 ≤ theta ∧ theta ≤ Real.pi / 6 ∧
      testingRains (appendixState theta) (1 - Real.sqrt 3 / 2) false <
        testingRains (appendixState theta) (1 - Real.sqrt 3 / 2) true := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
