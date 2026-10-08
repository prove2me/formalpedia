-- Prove2me | Theorems.Thm_StabGen_Uniform_bounded_differences_empirical
-- name    : StabGen.Uniform.bounded_differences_empirical
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:10:29.568464+00:00
-- url     : https://prove2.me/theorems/01f65d24-f296-4b39-b0ab-a30bb1e4da0c
-- title:
--   Proof of Theorem 12 — $R - R_{\mathrm{emp}}$ has bounded differences $4\beta + M/m$
-- statement:
--   Let $D$ be a probability distribution on $Z$ and let $A$ be a symmetric learning algorithm with uniform stability $\beta$ at sample size $m$, whose loss satisfies $0 \le \ell(A_T, z) \le M$ for every training set $T$ (of any size) and every $z \in Z$, with $(S, z) \mapsto \ell(A_S, z)$ measurable. For a sample $S \in Z^m$ write $R = R(A,S)$ and $R_{\mathrm{emp}} = R_{\mathrm{emp}}(A,S)$, and let $R^i$, $R^i_{\mathrm{emp}}$ be the same quantities for $S^i$ ($z_i$ replaced by $z_i'$). Then for every sample $S$, index $i$ and replacement point $z_i'$,
--
--   $$\big|(R - R_{\mathrm{emp}}) - (R^i - R^i_{\mathrm{emp}})\big| \le 4\beta + \frac{M}{m}.$$
--
--   This deterministic estimate combines $|R - R^i| \le 2\beta$ and $|R_{\mathrm{emp}} - R^i_{\mathrm{emp}}| \le 2\beta + M/m$; it says that the random variable $R - R_{\mathrm{emp}}$ satisfies the conditions of McDiarmid's inequality (Theorem 2) with $c_i = 4\beta + M/m$.
--
--   **Formalization Note** The paper's statement is about the two differences separately and their sum; the formalized statement is the bound on the difference of $R - R_{\mathrm{emp}}$, which is what Theorem 2 is applied to. The measurability hypothesis makes $R$ a genuine integral.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 507–508, proof of Theorem 12 (Eq. (13) and the following displays)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

open MeasureTheory FoundationsML.Stability

namespace StabGen.Uniform

/-- Bousquet & Elisseeff 2002, proof of Theorem 12, pp. 507–508: if `A` has uniform stability
`β` at size `m` and `0 ≤ ℓ(A_T, z) ≤ M` for every training set `T` and point `z`, then
`R − R_emp` has bounded differences `|(R − R_emp)(S) − (R − R_emp)(S^i)| ≤ 4β + M/m`. -/
theorem bounded_differences_empirical {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' : X × Y),
      |(GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
        - (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z')))
            - EmpiricalError L (StabGen.Hypothesis.replaceAt S i z') (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))))|
        ≤ 4 * β + M / m := by sorry

end StabGen.Uniform
