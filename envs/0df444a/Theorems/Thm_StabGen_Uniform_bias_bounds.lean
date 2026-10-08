-- Prove2me | Theorems.Thm_StabGen_Uniform_bias_bounds
-- name    : StabGen.Uniform.bias_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:10:56.948097+00:00
-- url     : https://prove2.me/theorems/8d4ca778-0283-4ae8-8dce-7d2270194bd0
-- title:
--   Proof of Theorem 12 — $\mathbb E_S[R - R_{\mathrm{emp}}] \le 2\beta$ and $\mathbb E_S[R - R_{\mathrm{loo}}] \le \beta$
-- statement:
--   Let $D$ be a probability distribution on $Z$, $m \ge 1$, and let $A$ be a symmetric learning algorithm with uniform stability $\beta$ at sample size $m$, whose loss satisfies $0 \le \ell(A_T, z) \le M$ for every training set $T$ and every $z$, with $(S, z) \mapsto \ell(A_S, z)$ measurable. Then, for $S \sim D^m$,
--
--   $$\mathbb E_S[R - R_{\mathrm{emp}}] \le 2\beta \qquad\text{and}\qquad \mathbb E_S[R - R_{\mathrm{loo}}] \le \beta.$$
--
--   These bound the means of the two generalization gaps. Together with the bounded differences of the gaps and McDiarmid's inequality they yield the tail bounds of Theorem 12, centred at $2\beta$ and $\beta$ respectively.
--
--   **Formalization Note** The expectations are Bochner integrals over the product measure $D^m$; the measurability and boundedness hypotheses make them genuine. The case $m = 0$ is excluded, as in the paper.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 508–509, proof of Theorem 12 (bound on E_S[R − R_emp]; "Lemma 7 along with (13)")

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

open MeasureTheory FoundationsML.Stability

namespace StabGen.Uniform

/-- Bousquet & Elisseeff 2002, proof of Theorem 12, pp. 508–509: if `A` has uniform stability
`β` at size `m ≥ 1` and `0 ≤ ℓ(A_T, z) ≤ M`, then `E_S[R − R_emp] ≤ 2β` and
`E_S[R − R_loo] ≤ β`, with `S ∼ D^m`. -/
theorem bias_bounds {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β) (hm : 1 ≤ m) :
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
        ∂(Measure.pi fun _ : Fin m => D) ≤ 2 * β) ∧
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S)
        ∂(Measure.pi fun _ : Fin m => D) ≤ β) := by sorry

end StabGen.Uniform
