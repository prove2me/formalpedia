-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_change_of_measure
-- name    : RetirePartialInfo.Duality.change_of_measure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:03.735588+00:00
-- url     : https://prove2.me/theorems/315ca7f5-4d10-438e-89c4-8ce2a26538b1
-- title:
--   Display after (6), p. 6 — Ẽ[M] = E[𝒵_t M] for F^S_t-measurable M
-- statement:
--   Work in the partial-information market of the mission: $Z$ is the exponential local martingale (3), Assumption 2.1 holds, $\tilde{\mathbb P}$ is defined by $d\tilde{\mathbb P}=Z_T\,d\mathbb P$, and $\mathcal Z_t=\mathbb E[Z_T\mid\mathcal F^S_t]$ is the projected density (6).
--
--   Let $t\in[0,T]$ and let $M$ be an $\mathcal F^S_t$-measurable random variable with $Z_TM$ integrable under $\mathbb P$. Then
--   $$\tilde{\mathbb E}[M]=\mathbb E[Z_TM]=\mathbb E\bigl[\mathbb E[Z_TM\mid\mathcal F^S_t]\bigr]=\mathbb E\bigl[\mathbb E[Z_T\mid\mathcal F^S_t]M\bigr]=\mathbb E[\mathcal Z_tM].$$
--
--   This identity turns expectations under the auxiliary measure of quantities the agent observes into expectations under $\mathbb P$ weighted by the projected density; it converts the budget constraint (8) into the $y_s$-weighted terms of the dual problem.
--
--   **Formalization Note.** The integrability of $Z_TM$ (equivalently of $M$ under $\tilde{\mathbb P}$) is tacit on the page and added. $\mathcal Z_t$ here is the conditional expectation itself. The Itô integral in $Z$ is the binder $I_\theta$ with hypothesis `IsItoIntegral`.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 6, display after (6)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **Change of measure**, display after (6), p. 6 (Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 6, display after (6)):
"for any `F^S_t`-measurable random variable `M`,
`Ẽ[M] = E[Z_T M] = E[E[Z_T M|F^S_t]] = E[E[Z_T|F^S_t]M] = E[𝒵_t M]`."

**Formalization Note.** Posed for `t ∈ [0, T]`, with `𝒵_t = E[Z_T | F^S_t]` the conditional
expectation itself (`calZ`) and `P̃ = Z_T · P` (`Pt`). The integrability of `Z_T M` under `P`
(equivalently of `M` under `P̃`) is tacit on the page and added. `Z` is built from the Itô binder
`Iθ`, constrained by `IsItoIntegral`; Assumption 2.1 makes `Z` a martingale. -/
theorem change_of_measure {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ : ℝ≥0 → Ω → ℝ) (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ)
    (h21 : Assumption21 p st Iθ) (t : ℝ≥0) (ht : (t : ℝ) ≤ p.T) (M : Ω → ℝ)
    (hM : StronglyMeasurable[FS p st t] M)
    (hint : Integrable (fun ω => Z p st Iθ p.Tn ω * M ω) st.P) :
    ∫ ω, M ω ∂(Pt p st Iθ) = ∫ ω, calZ p st Iθ t ω * M ω ∂st.P := by sorry

end RetirePartialInfo.Duality
