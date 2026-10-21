-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_11_case_1
-- name    : VWAPContract.Optimal.lemma_11_case_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:48.081643+00:00
-- url     : https://prove2.me/theorems/f97c94cb-7660-4410-a02b-e7d8f5e28c3d
-- title:
--   Lemma 11 (case 1), p. 45 (PDF 46) — $E[\sum_t\varepsilon_t v_t/\sum_s v_s]=\mu$ for nonnegative static trades
-- statement:
--   Let $x(\cdot)$ be a measurable function of the market conditions $\eta$ whose components are nonnegative at every positive $\eta$ (they need not sum to one), where $\eta$ takes positive values, let $v$ be a positive function on $\mathbb R_+\times\mathbb R_{++}$, and let $v_t=v(x_t(\eta),\eta_t)$ be the resulting market volumes. If $\mathbb E[\varepsilon_t\mid\eta]=\mu$ almost surely for every period, then
--
--   $$\mathbb E\!\left[\frac{\sum_{t=1}^T\varepsilon_t\, v(x_t(\eta),\eta_t)}{\sum_{s=1}^T v(x_s(\eta),\eta_s)}\right]=\mu.$$
--
--   The shock component of the realized market VWAP therefore has mean $\mu$ whatever the dealer trades. In the proof of Proposition 5 this cancels against the shock component of the trading cost (Lemma 10).
--
--   **Formalization Note** As in the paper's appendix the lemma is stated in a general framework: only the hypotheses of the page are assumed (in particular $v$ is any positive function, not necessarily of the form $xV(x/\eta)$), plus these necessary additions: $T\ge 1$, measurability of $\eta$, $\varepsilon$, $x$ and $v$, and integrability of each $\varepsilon_t$ (implicit in $\mathbb E[\varepsilon_t\mid\eta]$). The function $v$ is taken positive on all of $\mathbb R_+\times\mathbb R_{++}$. Volumes are positive, so the denominator never vanishes, and the volume weights lie in $[0,1]$, so the integrand is integrable. Only the paper's case 1 (static $x$) is formalized; case 2 (dynamic $x$, $v(x,\eta)=x+\eta$) belongs to §7.2.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), pp. 45–46 (PDF 46–47), Lemma 11, case 1

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_11_case_1 {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) [IsProbabilityMeasure M.P] (hT : 0 < T)
    (heta : Measurable M.eta) (heta_pos : ∀ ω t, 0 < M.eta ω t)
    (heps : Measurable M.eps)
    (heps_int : ∀ t, Integrable (fun ω => M.eps ω t) M.P)
    (hcond : ∀ t, M.P[fun ω => M.eps ω t | etaAlg M] =ᵐ[M.P] fun _ => M.mu)
    (hvol : Measurable (Function.uncurry M.vol))
    (hvpos : ∀ x e, 0 ≤ x → 0 < e → 0 < M.vol x e)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) (hXm : Measurable X)
    (hXnn : ∀ e : Fin T → ℝ, (∀ t, 0 < e t) → ∀ t, 0 ≤ X e t) :
    (∫ ω, (∑ t, M.eps ω t * mktVol M X ω t) /
      (∑ s, mktVol M X ω s) ∂M.P) = M.mu := by sorry

end VWAPContract.Optimal
