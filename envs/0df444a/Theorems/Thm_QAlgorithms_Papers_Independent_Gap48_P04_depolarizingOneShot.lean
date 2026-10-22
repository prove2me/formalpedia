-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P04_depolarizingOneShot
-- name    : QAlgorithms.Papers.Independent.Gap48.P04.depolarizingOneShot
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:57:57.067678+00:00
-- url     : https://prove2.me/theorems/fc4fe0f6-27a4-4b32-b026-3ccf5acd13b5
-- title:
--   Measured single-use capacity of the qubit depolarizing channel
-- statement:
--   Let $0\le\epsilon\le1$ and let $\mathcal D_\epsilon(X)=(1-\epsilon)X+(\epsilon/2)\operatorname{Tr}(X)I_2$ be the qubit depolarizing channel. Its measured single-use classical capacity is the maximum mutual information $I(X:Y)$, in bits, over finite normalized ensembles of density matrices at its input and finite POVMs at its output. With base-two logarithms and $0\log_2 0=0$, this maximum is attained and equals
--
--   $$C_{\mathrm{one}}(\mathcal D_\epsilon)=1-H_2(\epsilon/2)=1+\frac\epsilon2\log_2\frac\epsilon2+\left(1-\frac\epsilon2\right)\log_2\left(1-\frac\epsilon2\right),$$
--
--   where $H_2(s)=-s\log_2s-(1-s)\log_2(1-s)$. Every orthonormal basis $\{|u_0\rangle,|u_1\rangle\}$ attains this value when its states are used with probabilities $1/2,1/2$ and the output is measured in that basis. The resulting conditional law is
--
--   $$\Pr(Y=j\mid X=i)=\begin{cases}1-\epsilon/2&i=j,\\\epsilon/2&i\ne j.\end{cases}$$
--
--   This identifies the optimum with binary symmetric-channel mutual information for a single use; it makes no identification with the asymptotic classical capacity.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, PDF p. 3, Eq. (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

/-- Bennett--DiVincenzo--Smolin, PDF p.3, Eq.(5): measured single-use optimum,
attained by every equiprobable orthonormal basis with the matching measurement.
The PDF contains the coefficient p/2 missing from the text extraction. This is
not an assertion about the asymptotic classical capacity. -/
theorem depolarizingOneShot (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let N := QAlgorithms.QuditFidelity.depolarizingMap 2 (by decide) p
    let value := 1 - binEntropy2 (p/2)
    oneShotCapacity N = value ∧ IsGreatest (oneShotValues N) value ∧
    value = 1 + (p/2)*Real.logb 2 (p/2) + (1-p/2)*Real.logb 2 (1-p/2) ∧
    ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      IsPOVM (basisProjector U) ∧ (∀ i, IsDensityMatrix (basisProjector U i)) ∧
      mutualInfoBits (labelOutcomeLaw N (fun _ : Fin 2 => (1/2 : ℝ))
        (basisProjector U) (basisProjector U)) = value ∧
      ∀ i j : Fin 2, effectProb (basisProjector U j) (N (basisProjector U i)) =
        if i = j then 1-p/2 else p/2 := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P04
