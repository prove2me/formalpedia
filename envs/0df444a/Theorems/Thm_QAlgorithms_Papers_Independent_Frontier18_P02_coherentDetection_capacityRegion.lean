-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P02_coherentDetection_capacityRegion
-- name    : QAlgorithms.Papers.Independent.Frontier18.P02.coherentDetection_capacityRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:48:17.801905+00:00
-- url     : https://prove2.me/theorems/43cb93b8-5702-421a-a46a-d0d19bc9a2b0
-- title:
--   Equation (66), Appendix B (B9)–(B10): coherent-detection capacity regions
-- statement:
--   Fix a vacuum amplifier of finite gain $\kappa\ge1$ and a finite per-use input photon budget $N_S>0$. Both receivers use homodyne detection ($\xi=1/2$) or both use heterodyne detection ($\xi=1$). Consider the induced classical Gaussian broadcast channel with independent classical messages and separate measurable decoding functions. Its capacity region, defined by arbitrary classical block codes, vanishing average decoding error and unconditional average input power at most $N_S$ at each use, consists exactly of the nonnegative rate pairs $(R_B,R_C)$ for which one common $\lambda\in[0,1]$ satisfies
--
--   $$
--   R_B\le\xi\log_2\!\left(1+\frac{\lambda\kappa N_S}{\xi(\xi+\kappa-1)}\right),\qquad
--   R_C\le\xi\log_2\!\left(1+\frac{(1-\lambda)(\kappa-1)N_S}{\xi(\xi+\kappa-1)+\lambda(\kappa-1)N_S}\right).
--   $$
--
--   This identifies the performance attainable with the specified coherent measurements. The underlying classical codebooks are unrestricted; no Gaussian codebook hypothesis is imposed. This is a capacity statement for the induced classical channel under the paper's power convention.
--
--   **Formalization Note** The operational region is defined independently using positive message counts, product Gaussian noise laws, local measurable decoders, per-use message-averaged power constraints, and arbitrarily small error and rate slack at all sufficiently large positive block lengths. Homodyne uses one real component and heterodyne two, with component noise variance $(\xi+\kappa-1)/2$.
-- source:
--   Capacities of Quantum Amplifier Channels, arXiv:1605.04922v3, PDF p. 8, Equation (66), Appendix B (B9)–(B10): coherent-detection capacity regions

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P02

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.8, (66), and p.11, Appendix B, (B9)--(B10). For the vacuum
amplifier and fixed homodyne or heterodyne measurement, the capacity region
of the induced classical Gaussian broadcast channel equals the displayed
union. Physical gain=1 is included. Arbitrary non-Gaussian codebooks and
collective classical decoders are allowed in the operational definition. -/
theorem coherentDetection_capacityRegion (heterodyne : Bool)
    (gain budget : ℝ) (hgain : 1 ≤ gain) (hbudget : 0 < budget) :
    detectionCapacityRegion heterodyne gain budget =
      detectionRateRegion heterodyne gain budget := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P02

end
