-- Prove2me | Theorems.Thm_UnderstandingML_agnostic_lower_bound_log
-- name    : UnderstandingML.agnostic_lower_bound_log
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:54:39.905568+00:00
-- url     : https://prove2.me/theorems/62038359-5480-4307-a109-362ffb78fec5
-- title:
--   §28.2.1: for ε < 1/√2, δ ∈ (0,1) and m ≤ 0.5 log(1/(4δ))/ε², every algorithm has excess risk ≥ ε with probability ≥ δ under one of D₊, D₋
-- statement:
--   **§28.2.1.** For any $\epsilon < 1/\sqrt2$ and any $\delta \in (0,1)$, $m(\epsilon, \delta) \ge 0.5\log(1/(4\delta))/\epsilon^2$: for $m \le 0.5\log(1/(4\delta))/\epsilon^2$, $H$ is not learnable. With $c$ a point shattered by $H$ and $D_\pm$ the distributions with $D_b(\{(c, y)\}) = (1 + yb\epsilon)/2$, for every algorithm $A$ there exists $b$ such that
--   $$P\big[L_{D_b}(A(y)) - L_{D_b}(h_b) = \epsilon\big] \ge \tfrac12\Big(1 - \sqrt{1 - \sqrt{4\delta}}\Big) \ge \delta.$$
--
--   Formally: the event that the excess risk over the best hypothesis in $H$ is at least $\epsilon$ has probability at least $\delta$ under $D_b^m$ for some $b$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §28.2.1 pp. 393-395

import Definitions.Def_UnderstandingML_FundamentalProof

open MeasureTheory

namespace UnderstandingML

/-- **§28.2.1** (pp. 393–395). For any `ε < 1/√2` and any `δ ∈ (0, 1)`, `m(ε, δ) ≥ 0.5 log(1/(4δ))/ε²`:
if `m ≤ 0.5 log(1/(4δ))/ε²`, then for every algorithm `A` one of the two distributions `D₊, D₋`
concentrated on `(c, ±1)` (for a point `c` shattered by `H`) satisfies
`P_{S ∼ D^m}[L_D(A(S)) − min_{h ∈ H} L_D(h) ≥ ε] ≥ δ`. -/
theorem agnostic_lower_bound_log {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (H : Set (X → Bool)) (c : X) (hcT : ∃ h ∈ H, h c = true) (hcF : ∃ h ∈ H, h c = false)
    (ε δ : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / Real.sqrt 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (A : Learner (X × Bool) (X → Bool)) (m : ℕ)
    (hm : (m : ℝ) ≤ 0.5 * Real.log (1 / (4 * δ)) / ε ^ 2) :
    ∃ b : Fin 1 → Bool, ENNReal.ofReal δ ≤
      iidLaw (lowerBoundLaw (fun _ ↦ c) ε b) m {S | ∃ h ∈ H,
        risk loss01 (lowerBoundLaw (fun _ ↦ c) ε b) h + ε ≤
          risk loss01 (lowerBoundLaw (fun _ ↦ c) ε b) (A m S)} := by sorry

end UnderstandingML
