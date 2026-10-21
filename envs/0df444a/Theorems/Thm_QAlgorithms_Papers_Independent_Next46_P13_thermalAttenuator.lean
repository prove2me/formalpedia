-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_thermalAttenuator
-- name    : QAlgorithms.Papers.Independent.Next46.P13.thermalAttenuator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:10:37.203085+00:00
-- url     : https://prove2.me/theorems/5d68e8fa-ff1b-4abf-965b-4825cb773b2f
-- title:
--   Unnumbered §5.3: exact thermal attenuator evolution
-- statement:
--   For real occupation $n\ge0$, let $\omega_n=\frac1{n+1}\sum_{k\ge0}(\frac n{n+1})^k|k\rangle\langle k|$ be the one-mode thermal state. Write $g(n)=(n+1)\log(n+1)-n\log n$, with $0\log0=0$, and let $L_-(\rho)=a\rho a^\dagger-\frac12\{a^\dagger a,\rho\}$. Then $S(\omega_n)=g(n)$ and, for every $t\ge0$,
--
--   $$e^{tL_-}(\omega_n)=\omega_{e^{-t}n},\qquad
--   \left.\frac{d}{dt}S(e^{tL_-}(\omega_n))\right|_{0+}=
--   \begin{cases}-n\log(1+1/n),&n>0,\\0,&n=0.\end{cases}$$
--
--   This computes thermal attenuation and its entropy rate. The vacuum is fixed. Entropies are finite, and the asserted derivative is an existing right derivative, rather than a total derivative default.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 22, §5.3; Theorem 5 vacuum clause

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF pp.19,22, Section 5.3, and p.18 vacuum clause: exact thermal evolution,
finite entropy and right entropy derivative, including vacuum occupation zero. -/
theorem thermalAttenuator :
    ∀ n : ℝ, 0 ≤ n →
      B.ThermalRealized (2 * n + 1) ∧ C.fockEntropyNats (C.photonMeanThermalState n) = ENNReal.ofReal (C.g n) ∧
      (∀ t : ℝ, 0 ≤ t → ThermalChannelRealized (Real.exp (-t)) 0 (C.photonMeanThermalState n) ∧
        attenuator t (C.photonMeanThermalState n) = C.photonMeanThermalState (Real.exp (-t) * n) ∧
        C.fockEntropyNats (attenuator t (C.photonMeanThermalState n)) ≠ ⊤) ∧
      HasDerivWithinAt (fun t : ℝ => entropyReal (attenuator t (C.photonMeanThermalState n)))
        (if n = 0 then 0 else -n * Real.log (1 + 1 / n)) (Set.Ici 0) 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
