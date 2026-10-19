-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_higherOrderReversal
-- name    : QAlgorithms.Papers.Independent.Information100.P39.higherOrderReversal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:24:52.013433+00:00
-- url     : https://prove2.me/theorems/f0976b55-b411-46e0-bfae-c4b597f1942f
-- title:
--   Appendix A.3: distance-two CSS higher-order reversal
-- statement:
--   Consider the four-qubit CSS code with stabilizers $XXXX,ZZZZ,XXII$ and logical operators $\overline X=X_1X_3$, $\overline Z=Z_1Z_2$. Use normalized encoded basis states whose amplitudes are $1/2$ precisely when each pair $(1,2)$ and $(3,4)$ has parity equal to the logical bit. Apply the product Pauli laws
--
--   $$\nu_1=(49/50,1/50,0,0),\quad\nu_2=(49/50,0,1/50,0),\quad
--   \nu_3=(1/2,0,0,1/2),\quad\nu_4=(2/5,3/10,0,3/10).$$
--
--   The code detects every nonidentity single-qubit Pauli error. For the actual normalized noisy Choi state,
--
--   $$e^{-\Delta_2}=\frac{20417}{35858},\qquad
--    e^{-2\Delta_3}=\frac{138827}{450740},\qquad
--   \Delta_1\ge\Delta_2<\Delta_3.$$
--
--   The first three factors have independent-event representations. The fourth has Fourier triple $(2/5,-1/5,2/5)$, so neither it nor the full law admits one. There is an $\eta>0$ such that replacing only $\nu_4$ by any probability law differing from it by less than $\eta$ in every coordinate preserves the strict inequality $\Delta_2<\Delta_3$. This establishes a stable higher-order reversal without claiming that every lower-order inequality persists throughout that neighborhood.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 9, Appendix A.3: distance-two CSS higher-order reversal

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- Appendix A.3, PDF pp.9–10, Eqs.(S10)–(S12): detection, exact moments,
Shannon/collision ordering, the higher-order reversal, and its open relative
neighborhood among probability laws for the fourth factor. -/
theorem higherOrderReversal :
    ∃ hnu : Learning.IsDistribution (higherNoise (higherFactors 3)),
      IsEncoderFor higherGenerators higherEncoder ∧
      (∀ j : Fin 3, HasIndependentEvents (higherFactors j.castSucc)) ∧
      SparsePauliNoise.eigenvalueWHT (higherFactors 3) labelX = 2/5 ∧
      SparsePauliNoise.eigenvalueWHT (higherFactors 3) labelY = -1/5 ∧
      SparsePauliNoise.eigenvalueWHT (higherFactors 3) labelZ = 2/5 ∧
      ¬ HasIndependentEvents (higherFactors 3) ∧
      ¬ HasIndependentEvents (higherNoise (higherFactors 3)) ∧
      (∀ e : PauliLabel 4, labelWeight e = 1 →
        higherEncoderᴴ * SparsePauliNoise.labelOperator e * higherEncoder = 0) ∧
      Real.exp (-quantumDeficit higherEncoder (higherNoise (higherFactors 3)) hnu 2) = 20417/35858 ∧
      Real.exp (-2 * quantumDeficit higherEncoder (higherNoise (higherFactors 3)) hnu 3) = 138827/450740 ∧
      quantumDeficit higherEncoder (higherNoise (higherFactors 3)) hnu 2 ≤
        quantumDeficit higherEncoder (higherNoise (higherFactors 3)) hnu 1 ∧
      quantumDeficit higherEncoder (higherNoise (higherFactors 3)) hnu 2 <
        quantumDeficit higherEncoder (higherNoise (higherFactors 3)) hnu 3 ∧
      (∃ eta : ℝ, 0 < eta ∧ ∀ v : PauliLabel 1 → ℝ,
        Learning.IsDistribution v → (∀ e, |v e - higherFactors 3 e| < eta) →
        ∃ hv : Learning.IsDistribution (higherNoise v),
          quantumDeficit higherEncoder (higherNoise v) hv 2 <
            quantumDeficit higherEncoder (higherNoise v) hv 3) := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
