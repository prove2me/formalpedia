-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_10_case_1
-- name    : VWAPContract.Optimal.lemma_10_case_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:44.074869+00:00
-- url     : https://prove2.me/theorems/08b435c5-ef5e-447b-8968-fa1633144693
-- title:
--   Lemma 10 (case 1), p. 44 (PDF 45) — $\sum_t E[\varepsilon_t x_t(\eta)\mid\eta]=\mu$ a.s. when $\sum_t x_t(\eta)=1$ a.s.
-- statement:
--   Let $\eta=(\eta_t)_{t=1}^T$ and $\varepsilon=(\varepsilon_t)_{t=1}^T$ be random vectors on a probability space, and suppose each $\varepsilon_t$ has conditional mean $\mathbb E[\varepsilon_t\mid\eta]=\mu$ almost surely, for one constant $\mu$. Let $x(\cdot)=(x_t(\cdot))_{t=1}^T$ be functions of $\eta$ with $\sum_{t=1}^T x_t(\eta)=1$ almost surely. Then
--
--   $$\sum_{t=1}^T\mathbb E[\varepsilon_t x_t(\eta)\mid\eta]=\mu\quad\text{almost surely}.$$
--
--   The lemma identifies the conditional mean of the shock component of a trading cost $p\cdot x(\eta)$. It is used for the first-best cost calculation (Lemma 3) and the incentive analysis of Proposition 5.
--
--   **Formalization Note** This is the paper's case 1 (static $x$) only; case 2 (dynamic $x$) belongs to §7.2. As in the paper's appendix the lemma is stated in a general framework, not under the specialized model's assumptions on $h$, $v$, $u$. Added, because the conditional expectations must exist: $\eta$ and $x$ are measurable, each $\varepsilon_t$ and each product $\varepsilon_t x_t(\eta)$ is integrable (Lean's conditional expectation of a non-integrable function is $0$). The components $x_t$ need not be nonnegative, as on the page.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), pp. 44–45 (PDF 45–46), Lemma 10, case 1

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_10_case_1 {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) [IsProbabilityMeasure M.P]
    (heta : Measurable M.eta)
    (heps : ∀ t, Integrable (fun ω => M.eps ω t) M.P)
    (hcond : ∀ t, M.P[fun ω => M.eps ω t | etaAlg M] =ᵐ[M.P] fun _ => M.mu)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) (hXm : Measurable X)
    (hsum : ∀ᵐ ω ∂M.P, ∑ t, X (M.eta ω) t = 1)
    (hint : ∀ t, Integrable (fun ω => M.eps ω t * X (M.eta ω) t) M.P) :
    (fun ω => ∑ t, M.P[fun ω' => M.eps ω' t * X (M.eta ω') t | etaAlg M] ω)
      =ᵐ[M.P] fun _ => M.mu := by sorry

end VWAPContract.Optimal
