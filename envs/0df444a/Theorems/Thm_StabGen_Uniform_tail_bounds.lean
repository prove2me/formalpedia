-- Prove2me | Theorems.Thm_StabGen_Uniform_tail_bounds
-- name    : StabGen.Uniform.tail_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:10:56.079376+00:00
-- url     : https://prove2.me/theorems/9e0129ab-749b-45dd-b154-60eb0b26352d
-- title:
--   Proof of Theorem 12 — exponential tail bounds for $R - R_{\mathrm{emp}}$ and $R - R_{\mathrm{loo}}$
-- statement:
--   Let $D$ be a probability distribution on $Z$, $m \ge 1$, and let $A$ be a symmetric learning algorithm with uniform stability $\beta$ at sample size $m$, whose loss satisfies $0 \le \ell(A_T, z) \le M$ for every training set $T$ and every $z$, with $(S, z) \mapsto \ell(A_S, z)$ measurable. Then for every $\epsilon > 0$, with $S \sim D^m$,
--
--   $$P_S\big[R - R_{\mathrm{emp}} > \epsilon + 2\beta\big] \le \exp\Big(-\frac{2m\epsilon^2}{(4m\beta + M)^2}\Big),$$
--
--   and, if $A$ has uniform stability $\beta$ at sample size $m-1$ as well,
--
--   $$P_S\big[R - R_{\mathrm{loo}} > \epsilon + \beta\big] \le \exp\Big(-\frac{2m\epsilon^2}{(4m\beta + M)^2}\Big).$$
--
--   These are the bounds of Theorem 12 before the confidence level is substituted: setting the right side equal to $\delta$ gives (11) and (12).
--
--   **Formalization Note** The paper writes the denominator of the second bound as $(m(4\beta_m) + M)^2$, which equals $(4m\beta + M)^2$. The size-$(m-1)$ stability encodes the paper's convention $\beta_{m-1} \le \beta_m$ (p. 504) and is required only for the leave-one-out bound. If $4m\beta + M = 0$, the displayed fraction has zero denominator; the formal statement uses the natural zero tail bound because the loss is then identically zero.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 508–509, proof of Theorem 12

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

open MeasureTheory FoundationsML.Stability

namespace StabGen.Uniform

/-- Bousquet & Elisseeff 2002, proof of Theorem 12, pp. 508–509: if `A` has uniform stability
`β` at size `m ≥ 1` and `0 ≤ ℓ(A_T, z) ≤ M`, then for every `ε > 0`
`P_S[R − R_emp > ε + 2β] ≤ exp(−2mε² / (4mβ + M)²)`, and, if `A` also has uniform stability
`β` at size `m − 1`, `P_S[R − R_loo > ε + β] ≤ exp(−2mε² / (4mβ + M)²)`. -/
theorem tail_bounds {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin m => D)
        {S | ε + 2 * β <
          GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S))}
      ≤ (if 4 * m * β + M = 0 then 0
         else ENNReal.ofReal (Real.exp (-(2 * m * ε ^ 2) / (4 * m * β + M) ^ 2))) ∧
    (HasUniformStability L A (m - 1) β →
      (Measure.pi fun _ : Fin m => D)
          {S | ε + β < GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S}
        ≤ (if 4 * m * β + M = 0 then 0
           else ENNReal.ofReal (Real.exp (-(2 * m * ε ^ 2) / (4 * m * β + M) ^ 2)))) := by sorry

end StabGen.Uniform
