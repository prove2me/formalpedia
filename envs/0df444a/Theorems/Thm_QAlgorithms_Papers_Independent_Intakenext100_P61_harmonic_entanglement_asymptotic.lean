-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_harmonic_entanglement_asymptotic
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.harmonic_entanglement_asymptotic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:20:18.422146+00:00
-- url     : https://prove2.me/theorems/36c4ce9a-073b-4781-a2e3-553d0b68a37f
-- title:
--   §IV, unnumbered: entropy of the harmonic embezzling family
-- statement:
--   Let $|\mu_n\rangle=H_n^{-1/2}\sum_{i=1}^ni^{-1/2}|i,i\rangle$, where $H_n=\sum_{i=1}^n1/i$, and let $E(\mu_n)=S(\operatorname{Tr}_B|\mu_n\rangle\langle\mu_n|)$ be its entropy of entanglement in bits. Then
--
--   $$\lim_{n\to\infty}\frac{E(\mu_n)}{\log_2 n}=\frac12.$$
--
--   This is a first-order asymptotic, rather than an exact finite-size entropy identity. It compares the harmonic family's entanglement with its preparation cost.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 7, §IV, unnumbered: entropy of the harmonic embezzling family

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF p.7, unnumbered: first-order entropy asymptotic of the harmonic family.
The finite n=0,1 totalized quotient values do not affect the limit at infinity. -/
theorem harmonic_entanglement_asymptotic :
    Filter.Tendsto (fun n : ℕ => entropyOne (aliceDensity (harmonicState n)) / logTwo n)
      Filter.atTop (nhds (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
