-- Prove2me | Theorems.Thm_StabGen_Uniform_bounded_differences_loo
-- name    : StabGen.Uniform.bounded_differences_loo
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:10:44.528006+00:00
-- url     : https://prove2.me/theorems/cce6a6ca-55d9-497f-b49b-82c217b1a004
-- title:
--   Proof of Theorem 12 — $R - R_{\mathrm{loo}}$ has bounded differences $4\beta + M/m$
-- statement:
--   Let $D$ be a probability distribution on $Z$ and let $A$ be a symmetric learning algorithm with uniform stability $\beta$ at sample sizes $m$ and $m-1$, whose loss satisfies $0 \le \ell(A_T, z) \le M$ for every training set $T$ and every $z \in Z$, with $(S, z) \mapsto \ell(A_S, z)$ measurable. With $R = R(A,S)$, $R_{\mathrm{loo}} = R_{\mathrm{loo}}(A,S)$ and $R^i$, $R^i_{\mathrm{loo}}$ the same quantities for $S^i$, for every sample $S \in Z^m$, index $i$ and replacement point $z_i'$,
--
--   $$\big|(R - R_{\mathrm{loo}}) - (R^i - R^i_{\mathrm{loo}})\big| \le 4\beta + \frac{M}{m}.$$
--
--   In the paper this is $|R - R^i| \le 2\beta_m$ together with $|R_{\mathrm{loo}} - R^i_{\mathrm{loo}}| \le 2\beta_{m-1} + M/m \le 2\beta_m + M/m$: the random variable $R - R_{\mathrm{loo}}$ satisfies the conditions of McDiarmid's inequality with $c_i = 4\beta + M/m$.
--
--   **Formalization Note** The leave-one-out error involves the algorithm trained on sets of size $m-1$, so its variation is controlled by the stability $\beta_{m-1}$. The paper assumes the stability is non-increasing in the sample size and bounds $\beta_{m-1}$ by $\beta_m$ (p. 504); here this convention is the explicit hypothesis that $A$ has uniform stability $\beta$ at size $m - 1$ as well as at size $m$. At $m = 1$ that hypothesis is vacuous.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 508–509, proof of Theorem 12 (leave-one-out part)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

open MeasureTheory FoundationsML.Stability

namespace StabGen.Uniform

/-- Bousquet & Elisseeff 2002, proof of Theorem 12, p. 508: if `A` has uniform stability `β`
at sizes `m` and `m − 1` and `0 ≤ ℓ(A_T, z) ≤ M` for every training set `T` and point `z`,
then `R − R_loo` has bounded differences `|(R − R_loo)(S) − (R − R_loo)(S^i)| ≤ 4β + M/m`. -/
theorem bounded_differences_loo {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β)
    (hstab' : HasUniformStability L A (m - 1) β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' : X × Y),
      |(GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S)
        - (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z')))
            - StabGen.Hypothesis.looError L A (StabGen.Hypothesis.replaceAt S i z'))|
        ≤ 4 * β + M / m := by sorry

end StabGen.Uniform
