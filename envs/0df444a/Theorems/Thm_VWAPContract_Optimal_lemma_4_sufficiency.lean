-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_4_sufficiency
-- name    : VWAPContract.Optimal.lemma_4_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:56.084781+00:00
-- url     : https://prove2.me/theorems/c158505d-c3d9-4c64-86b2-623d838e1ff4
-- title:
--   Lemma 4 (i)–(ii), pp. 21–22 (PDF 22–23) — incentive compatibility of $x^{FB}$ and full insurance suffice for optimality
-- statement:
--   Let $\tau$ be a measurable contract. Suppose the first-best policy is incentive compatible under $\tau$ and the contract pays exactly its realized market trading cost almost surely:
--
--   $$\mathbb E[u(\tau-p\cdot x^{\mathrm{FB}})]\ge\mathbb E[u(\tau-p\cdot\widehat x)]\quad\text{for every admissible static }\widehat x,\qquad \tau(p,v(x^{\mathrm{FB}},\eta))=p\cdot x^{\mathrm{FB}}\quad\text{almost surely}.$$
--
--   Then $\tau$ is an optimal contract for the client. These are the sufficient conditions (i) and (ii) of Lemma 4; the lemma's separate necessity claim is outside this milestone.
--
--   **Formalization Note** Incentive compatibility compares deviations whose expected utility is finite. The almost sure payment identity and the model assumptions supply integrability at the first-best policy.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), pp. 21–22 (PDF 22–23), Lemma 4, first sentence with conditions (i) and (ii) (sufficiency only)

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_4_sufficiency {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (hM : M.Standing)
    (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (hτ : IsContract τ) (hIC : IC M τ xFB)
    (hPay : pay M τ xFB =ᵐ[M.P] cost M xFB) :
    IsOptimal M τ := by sorry

end VWAPContract.Optimal
