-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_lemma_3_14_properties_of_calibration_function
-- name    : SupportVectorMachines.Calibration.lemma_3_14_properties_of_calibration_function
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:11.98098+00:00
-- url     : https://prove2.me/theorems/0a14b407-726f-400d-bb5c-ec41691b39f8
-- title:
--   Lemma 3.14 — the calibration function controls the minimizer sets, and Eq. (3.16)
-- statement:
--   This is Lemma 3.14 (Properties of the calibration function) of Steinwart & Christmann,
--   *Support Vector Machines* (Springer 2008, p. 58), the basic toolkit for the calibration
--   function, and the result Theorem 3.17's own proof cites directly ("By part i) of Lemma
--   3.14...").
--
--   Let $L_{\mathrm{tar}}, L_{\mathrm{sur}}$ be losses and $Q$ a distribution on the label space.
--   For all $x \in X$ and $\varepsilon \in [0,\infty]$:
--
--   1. $M_{L_{\mathrm{sur}},Q,x}(\delta_{\max}(\varepsilon,Q,x)) \subseteq M_{L_{\mathrm{tar}},Q,x}(\varepsilon)$.
--   2. $M_{L_{\mathrm{sur}},Q,x}(\delta) \not\subseteq M_{L_{\mathrm{tar}},Q,x}(\varepsilon)$
--      whenever $\delta > \delta_{\max}(\varepsilon,Q,x)$.
--   3. If $C^*_{L_{\mathrm{tar}},Q,x} < \infty$ and $C^*_{L_{\mathrm{sur}},Q,x} < \infty$, then for
--      every $t \in \mathbb R$ (Eq. (3.16)),
--      $$
--      \delta_{\max}\big(C_{L_{\mathrm{tar}},Q,x}(t) - C^*_{L_{\mathrm{tar}},Q,x},\, Q,\, x\big)
--        \le C_{L_{\mathrm{sur}},Q,x}(t) - C^*_{L_{\mathrm{sur}},Q,x}.
--      $$
--
--   Parts 1-2 together show $\delta_{\max}(\varepsilon,Q,x)$ is literally the largest $\delta$ for
--   which the surrogate's $\delta$-approximate minimizers are trapped inside the target's
--   $\varepsilon$-approximate minimizers; Eq. (3.16) is the pointwise inequality that, once
--   integrated over $x$, will later yield inequalities between excess risks.
--
--   **Formalization Note** No `IsProbabilityMeasure Q` hypothesis is added: re-reading the proof
--   (p. 59) directly, no step uses $Q$ having total mass $1$, only the inner-risk machinery,
--   which is well-defined for any measure — a disclosed, harmless generalization, the same kind
--   the `01-loss-functions` mission made for Lemma 2.23's convexity hypothesis.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 58, Lemma 3.14, Eq. (3.16)

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Lemma 3.14 (Properties of the calibration function), p. 58: for all `x ∈ X` and
`ε ∈ [0,∞]`: i) `M_{Lsur,Q,x}(δmax(ε,Q,x)) ⊆ M_{Ltar,Q,x}(ε)`; ii) `M_{Lsur,Q,x}(δ) ⊄
M_{Ltar,Q,x}(ε)` whenever `δ > δmax(ε,Q,x)`; and, if `C*_{Ltar,Q,x} < ∞` and `C*_{Lsur,Q,x} < ∞`,
Eq. (3.16): for all `t ∈ ℝ`,
`δmax(C_{Ltar,Q,x}(t) - C*_{Ltar,Q,x}, Q, x) ≤ C_{Lsur,Q,x}(t) - C*_{Lsur,Q,x}`. -/
theorem lemma_3_14_properties_of_calibration_function {X : Type*} (Ltar Lsur : Loss X)
    (Q : Measure ℝ) (x : X) (ε : ENNReal) :
    (approxMinimizers Lsur Q x (calibrationFunction Ltar Lsur Q x ε) ⊆
        approxMinimizers Ltar Q x ε) ∧
    (∀ δ : ENNReal, calibrationFunction Ltar Lsur Q x ε < δ →
      ¬ (approxMinimizers Lsur Q x δ ⊆ approxMinimizers Ltar Q x ε)) ∧
    (minInnerRisk Ltar Q x < ⊤ → minInnerRisk Lsur Q x < ⊤ →
      ∀ t : ℝ, calibrationFunction Ltar Lsur Q x
          (innerRisk Ltar Q x t - minInnerRisk Ltar Q x) ≤
        innerRisk Lsur Q x t - minInnerRisk Lsur Q x) := by sorry

end SupportVectorMachines.Calibration
