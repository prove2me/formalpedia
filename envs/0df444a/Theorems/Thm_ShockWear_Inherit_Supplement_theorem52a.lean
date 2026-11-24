-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem52a
-- name    : ShockWear.Inherit.Supplement.theorem52a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:55:56.610298+00:00
-- url     : https://prove2.me/theorems/74930074-9c41-4fd3-8707-49ec2fb96c72
-- title:
--   Theorem 5.2 (a) — An IHRA random threshold gives IHRA life for every nonnegative damage law
-- statement:
--   Let $F$ be any probability law on $[0,\infty)$ and let the independent threshold have probability law $G$ with $G(0)=0$. Define the literal non-strict survival coefficients and Poisson mixture by
--
--   $$
--   \bar P_k=\int_0^\infty F^{(k)}(x)\,dG(x),\qquad
--   \bar H(t)=\sum_{k=0}^\infty\bar P_k e^{-\lambda t}\frac{(\lambda t)^k}{k!},\quad\lambda>0.
--   $$
--
--   If $G$ is IHRA, then
--
--   $$
--   \bar H(s)^{1/s}\ge\bar H(t)^{1/t}\qquad(0<s\le t).
--   $$
--
--   The assertion holds for every damage law, including laws with atoms, without assuming that the discrete roots $\bar P_k^{1/k}$ decrease. The source explicitly leaves that intermediate question unresolved under IHRA alone.
--
--   **Formalization Note** The source states the convenient no-common-discontinuities convention on p. 642; we state the literal integral (5.1) also at shared atoms. There it is $E[\bar G(S_k-)]$, not $E[\bar G(S_k)]$. The extension follows by shifting the IHRA threshold by positive amounts tending to zero, avoiding the countably many common discontinuities, and taking bounded-convergence limits; positive deterministic shifts preserve IHRA. The published `randP`, `survOf` and `IsIHRA` are used unchanged.
--
--   Differences from the source:
--   - encoding: nonnegative damage distribution F and threshold distribution G with G(0)=0 → probability measures μ,ν on ℝ with μ(−∞,0)=0 and ν(−∞,0]=0; reason: CDFs are masses of closed lower intervals; all atoms and nonnegative damage laws are represented
--   - generalization: p. 642 assumes convolution CDFs and G have no common discontinuities → the literal integral (5.1) is allowed at shared atoms; reason: positive shifts preserve IHRA and converge to non-strict survival; bounded convergence passes the source result to the limit
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 643, Theorem 5.2 (a); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem52a (lam : ℝ) (hlam : 0 < lam)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iic 0) = 0)
    (hG : ShockWear.RandThreshold.IsIHRA (ShockWear.RandThreshold.survOf ν))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ShockWear.RandThreshold.IsIHRA
      (ShockWear.RandThreshold.shockSurv lam (ShockWear.RandThreshold.randP μ ν)) := by sorry

end ShockWear.Inherit.Supplement
