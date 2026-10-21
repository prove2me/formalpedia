-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_3_first_best
-- name    : VWAPContract.Optimal.lemma_3_first_best
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:48.41459+00:00
-- url     : https://prove2.me/theorems/9a87f5d8-92c4-4e37-a888-c30bfd6272c0
-- title:
--   Lemma 3, p. 21 (PDF 22) — the first-best trading policy is $x^{FB}(\eta)=(\eta_t/\sum_s\eta_s)_t$
-- statement:
--   In the specialized model, the volume-participation policy
--
--   $$x^{FB}(\eta)=\left(\frac{\eta_t}{\sum_{s=1}^T\eta_s}\right)_{t=1}^T$$
--
--   is first best: its expected trading cost conditional on $\eta$ is almost surely no larger than that of any other static trading policy. It is moreover *the* first-best policy: every first-best policy $x(\cdot)$ satisfies $x(\eta)=x^{FB}(\eta)$ almost surely.
--
--   The first best is the benchmark that the client's optimal contract must reach: by Lemma 4, a contract that insures the dealer at $x^{FB}$ and makes $x^{FB}$ incentive compatible is optimal.
--
--   **Formalization Note** "First best" compares $\mathbb E[p\cdot x(\eta)\mid\eta]$ almost surely against every static policy whose trading cost is integrable (conditional expectations of non-integrable functions are not meaningful in Lean). Uniqueness is almost sure equality of the realized schedules $x(\eta)$ and $x^{FB}(\eta)$.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 21 (PDF 22), Lemma 3, first sentence; uniqueness p. 20 (PDF 21), §5.1

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_3_first_best {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (hM : M.Standing) :
    IsFirstBest M xFB ∧
    ∀ X, IsFirstBest M X →
      (fun ω => X (M.eta ω)) =ᵐ[M.P] fun ω => xFB (M.eta ω) := by sorry

end VWAPContract.Optimal
