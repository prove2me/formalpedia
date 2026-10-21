-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_3_expected_cost
-- name    : VWAPContract.Optimal.lemma_3_expected_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:50.205207+00:00
-- url     : https://prove2.me/theorems/7af05e0b-40d0-454f-80fc-ecb2d64cc1b7
-- title:
--   Lemma 3, p. 21 (PDF 22) — $E[p\cdot x^{FB}(\eta)]=\mu+E[h(1/\sum_t\eta_t)]$
-- statement:
--   In the specialized model, the trading cost of the first-best policy $x^{FB}$ is integrable and its expectation is
--
--   $$\mathbb E\big[p\cdot x^{FB}(\eta)\big]=\mu+\mathbb E\!\left[h\!\left(\frac{1}{\sum_{t=1}^T\eta_t}\right)\right].$$
--
--   This is the lowest expected cost of buying the share, and hence a lower bound on what the client must expect to pay under any feasible contract.
--
--   **Formalization Note** The model assumes that $h(1/\sum_t\eta_t)$ is integrable; the integrability of the cost is part of the conclusion.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 21 (PDF 22), Lemma 3, second sentence

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_3_expected_cost {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (hM : M.Standing) :
    Integrable (cost M xFB) M.P ∧
    (∫ ω, cost M xFB ω ∂M.P) = M.mu + ∫ ω, M.h (1 / ∑ t, M.eta ω t) ∂M.P := by sorry

end VWAPContract.Optimal
