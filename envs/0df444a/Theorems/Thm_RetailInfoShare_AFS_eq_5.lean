-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_eq_5
-- name    : RetailInfoShare.AFS.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:00.472184+00:00
-- url     : https://prove2.me/theorems/6d031cc6-451a-41f1-a0fa-bb9e010d1e3d
-- title:
--   Equation (5), p. 14 — posterior mean of u under full sharing: σ/(σ + (t+η)/N) times the average shared signal
-- statement:
--   Assume the standing assumptions. Let $M$ be a noise matrix and $j$ a seller who receives all $N$ signals with a common finite noise level $\eta \ge 0$, i.e. $m_{ij} = \eta$ for every $i$. Then the posterior mean of the demand shock given seller $j$'s information is
--   $$E\big[u \,\big|\, \hat x_{1j}, \dots, \hat x_{Nj}\big] = \frac{\sigma}{\sigma + \frac{t+\eta}{N}} \cdot \frac1N \sum_{i=1}^N \hat x_{ij} \qquad \text{almost surely.}$$
--
--   This is the Gaussian updating formula behind the paper's observation that, under full sharing, receiving all signals is equivalent to receiving their average. It drives every closed form in the analysis of the AFS format.
--
--   **Formalization Note.** In the paper the receiving seller is $i$ and the sum runs over the signal index $j$ ($\hat x_{ji}$ is signal $j$ sent to seller $i$); here the receiver is $j$. Only the column of $M$ for seller $j$ is constrained; the rest of $M$ is arbitrary, which is harmless since seller $j$'s information depends only on that column.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), p. 14, Equation (5)

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem eq_5 (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (j : Fin P.N) (η : ℝ≥0) (hη : ∀ i, M i j = (η : ℝ≥0∞)) :
    μ[Z.u | info Z M j] =ᵐ[μ] fun ω =>
      (P.sig : ℝ) / ((P.sig : ℝ) + ((P.t : ℝ) + (η : ℝ)) / P.N) *
        ((1 / (P.N : ℝ)) * ∑ i, xhat Z M i j ω) := by sorry

end RetailInfoShare.AFS
