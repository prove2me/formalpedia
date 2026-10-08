-- Prove2me | Theorems.Thm_StabGen_Uniform_uniform_stability_generalization_bound
-- name    : StabGen.Uniform.uniform_stability_generalization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:11:08.701986+00:00
-- url     : https://prove2.me/theorems/4459232e-6f13-4b7f-8949-76d3e3391a0f
-- title:
--   Theorem 12 — exponential generalization bounds for uniformly stable algorithms
-- statement:
--   Let $Z = X \times Y$ carry a probability distribution $D$, let $S = (z_1, \dots, z_m)$ be drawn i.i.d. from $D$, and let $A$ be a symmetric learning algorithm. Let $\ell$ be a loss such that $0 \le \ell(A_S, z) \le M$ for all $z \in Z$ and all training sets $S$, and suppose $A$ has uniform stability $\beta$ with respect to $\ell$: removing any one of the $m$ training examples changes $\ell(A_S, z)$ by at most $\beta$, for every $z$. Write $R$, $R_{\mathrm{emp}}$ and $R_{\mathrm{loo}}$ for the generalization, empirical and leave-one-out errors of $A$ on $S$. Then for any $m \ge 1$ and any $\delta \in (0, 1)$, each of the following bounds holds (separately) with probability at least $1 - \delta$ over the random draw of $S$:
--
--   $$R \le R_{\mathrm{emp}} + 2\beta + (4m\beta + M)\sqrt{\frac{\ln(1/\delta)}{2m}}, \qquad (11)$$
--
--   $$R \le R_{\mathrm{loo}} + \beta + (4m\beta + M)\sqrt{\frac{\ln(1/\delta)}{2m}}. \qquad (12)$$
--
--   This is the main result of the paper. When $\beta$ scales as $1/m$, both bounds are of order $1/\sqrt m$, and they apply to any algorithm whose uniform stability can be computed, regardless of the size of its hypothesis space; the later sections compute $\beta$ for regularization algorithms in reproducing kernel Hilbert spaces.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: the $D^m$-measure of the set of samples on which the bound fails is at most $\delta$. The two bounds are two separate statements, joined by a conjunction; they are not claimed jointly. The paper assumes that the stability is non-increasing in the sample size and bounds $\beta_{m-1}$ by $\beta_m$ (p. 504); the leave-one-out bound (12) uses stability at size $m-1$, so it carries the explicit hypothesis that $A$ has uniform stability $\beta$ at size $m-1$ as well; (11) does not. The paper's standing assumption that all functions are measurable is the hypothesis that $(S, z) \mapsto \ell(A_S, z)$ is measurable at every sample size. The loss bound holds for training sets of every size. $\ln$ is the natural logarithm.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 507, Theorem 12, Eqs. (11) and (12)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

open MeasureTheory FoundationsML.Stability

namespace StabGen.Uniform

/-- **Theorem 12** (Bousquet & Elisseeff 2002, p. 507). Let `A` have uniform stability `β` with
respect to a loss `ℓ` with `0 ≤ ℓ(A_S, z) ≤ M` for all `z` and all training sets `S`. Then for
any `m ≥ 1` and `δ ∈ (0, 1)`, each of the following holds (separately) with probability at least
`1 − δ` over `S ∼ D^m`:
(11) `R ≤ R_emp + 2β + (4mβ + M)√(ln(1/δ)/(2m))`;
(12) `R ≤ R_loo + β + (4mβ + M)√(ln(1/δ)/(2m))`, where (12) also uses uniform stability `β`
at size `m − 1` (the paper's convention `β_{m−1} ≤ β_m`, p. 504). -/
theorem uniform_stability_generalization_bound {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β)
    (hm : 1 ≤ m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin m => D)
        {S | EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)) + 2 * β
              + (4 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))
            < GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))}
      ≤ ENNReal.ofReal δ ∧
    (HasUniformStability L A (m - 1) β →
      (Measure.pi fun _ : Fin m => D)
          {S | StabGen.Hypothesis.looError L A S + β + (4 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))
              < GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))}
        ≤ ENNReal.ofReal δ) := by sorry

end StabGen.Uniform
