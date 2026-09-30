-- Prove2me | Theorems.Thm_UnderstandingML_ml_rule_optimal
-- name    : UnderstandingML.ml_rule_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:54:51.066863+00:00
-- url     : https://prove2.me/theorems/717df6c9-7f48-4bfa-88be-5f94c9b8a0ba
-- title:
--   Lemma 28.1: the Maximum-Likelihood (majority-vote) rule minimizes the average over b ∈ {±1}^d of E_{S∼D_b^m}[L_{D_b}(A(S))] among all algorithms
-- statement:
--   **Lemma 28.1.** Among all algorithms, Equation (28.4) is minimized for $A$ being the Maximum-Likelihood algorithm $A_{ML}$, defined as $\forall i$, $A_{ML}(S)(c_i) = \operatorname{sign}\big(\sum_{r : x_r = c_i} y_r\big)$.
--
--   Formally: for every majority rule $A_{ML}$ (ties arbitrary) and every algorithm $A$, $\sum_b \mathbb{E}_{S \sim D_b^m}[L_{D_b}(A_{ML}(S))] \le \sum_b \mathbb{E}_{S \sim D_b^m}[L_{D_b}(A(S))]$; the term $\min_{h \in H}L_{D_b}(h)$ of (28.4) is the same on both sides. $C$ injective, $\rho \in [0, 1)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §28.2.2 pp. 396-397, Lemma 28.1 with its proof

import Definitions.Def_UnderstandingML_FundamentalProof

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 28.1** (p. 396). Among all algorithms, Equation (28.4), the average over
`b ∼ U({±1}^d)` of `E_{S ∼ D_b^m}[L_{D_b}(A(S)) − min_{h ∈ H} L_{D_b}(h)]`, is minimized for `A`
being the Maximum-Likelihood algorithm `A_ML`, `A_ML(S)(cᵢ) = sign(∑_{r : x_r = cᵢ} y_r)`.
Stated as: every majority rule has average risk at most that of any algorithm (the
`min_h L_{D_b}` term is the same on both sides). `C` injective, `ρ ∈ [0, 1)`. -/
theorem ml_rule_optimal {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {d : ℕ}
    (C : Fin d → X) (hC : Function.Injective C) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (m : ℕ)
    (AML A : Learner (X × Bool) (X → Bool)) (hML : IsMajorityRule C AML) :
    ∑ b : Fin d → Bool, ∫ S, risk loss01 (lowerBoundLaw C ρ b) (AML m S)
        ∂(iidLaw (lowerBoundLaw C ρ b) m) ≤
      ∑ b : Fin d → Bool, ∫ S, risk loss01 (lowerBoundLaw C ρ b) (A m S)
        ∂(iidLaw (lowerBoundLaw C ρ b) m) := by sorry

end UnderstandingML
