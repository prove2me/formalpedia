-- Prove2me | Theorems.Thm_UnderstandingML_agnostic_lower_bound_d
-- name    : UnderstandingML.agnostic_lower_bound_d
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:55:26.030569+00:00
-- url     : https://prove2.me/theorems/bd02b1df-b0e2-4407-b136-d6844b58a9e5
-- title:
--   §28.2.2: for ε < 1/(8√2) and m < d/(512ε²), every algorithm has excess risk ≥ ε with probability ≥ 1/8 under some D_b, so m(ε, 1/8) ≥ 8d/ε²
-- statement:
--   **§28.2.2.** We shall now prove that for every $\epsilon < 1/(8\sqrt2)$ we have that $m(\epsilon, \delta) \ge \frac{8d}{\epsilon^2}$ (for $\delta \le 1/8$). Choosing $\rho = 8\epsilon$ we conclude that if $m < \frac{d}{512\epsilon^2}$, then with probability of at least $1/8$ we will have $L_D(A(S)) - \min_{h \in H}L_D(h) \ge \epsilon$.
--
--   Formally: $C = \{c_1, \dots, c_d\}$ shattered by $H$, and the distribution is one of the $D_b$ with $\rho = 8\epsilon$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §28.2.2 p. 398 (via Lemma B.1 with ρ = 8ε)

import Definitions.Def_UnderstandingML_FundamentalProof

open MeasureTheory

namespace UnderstandingML

/-- **§28.2.2** (p. 398). For every `ε < 1/(8√2)`, `m(ε, 1/8) ≥ 8d/ε²`: choosing `ρ = 8ε`, if
`m < d/(512 ε²)` then for any algorithm `A` there is a distribution `D_b` such that with
probability of at least `1/8` over `S ∼ D^m`, `L_D(A(S)) − min_{h ∈ H} L_D(h) ≥ ε`. Here
`C = {c₁, …, c_d}` is shattered by `H`. -/
theorem agnostic_lower_bound_d {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (H : Set (X → Bool)) {d : ℕ} (C : Fin d → X) (hC : Function.Injective C)
    (hshat : ∀ g : Fin d → Bool, ∃ h ∈ H, ∀ i, h (C i) = g i) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε < 1 / (8 * Real.sqrt 2)) (m : ℕ) (hm : (m : ℝ) < d / (512 * ε ^ 2))
    (A : Learner (X × Bool) (X → Bool)) :
    ∃ b : Fin d → Bool, ENNReal.ofReal (1 / 8) ≤
      iidLaw (lowerBoundLaw C (8 * ε) b) m {S | ∃ h ∈ H,
        risk loss01 (lowerBoundLaw C (8 * ε) b) h + ε ≤
          risk loss01 (lowerBoundLaw C (8 * ε) b) (A m S)} := by sorry

end UnderstandingML
