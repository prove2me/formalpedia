-- Prove2me | Theorems.Thm_UnivESD_LogDet_eq_8_1
-- name    : UnivESD.LogDet.eq_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:05.771866+00:00
-- url     : https://prove2.me/theorems/566d8a45-b197-42fa-8b48-049712b693a7
-- title:
--   (8.1), p. 2054 — the logarithmic potential $\int\log|w-z|\,d\mu(w)$ is finite for a.e. $z$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb C$ with finite second moment, $\int_{\mathbb C}|w|^2\,d\mu(w)<\infty$. Then the function
--   $$z\longmapsto\int_{\mathbb C}\big|\log|w-z|\big|\,d\mu(w)$$
--   is locally integrable on $\mathbb C$ with respect to Lebesgue measure, and consequently, for Lebesgue-almost every $z\in\mathbb C$, $w\mapsto\log|w-z|$ is $\mu$-integrable:
--   $$\int_{\mathbb C}\log|w-z|\,d\mu(w)\ \text{is finite for almost every } z .$$
--
--   In the proof of Theorem 1.15 this is what makes the strong law of large numbers applicable to $\frac1n\sum_{i}\log|\lambda_i-z|$ for i.i.d. samples $\lambda_i$ of $\mu$.
--
--   **Formalization Note** Local integrability is stated as finiteness of $\int_K\int|\log|w-z||\,d\mu(w)\,dz$ (lower Lebesgue integrals) on every compact $K$. Because $\int|w|^2\,d\mu<\infty$, the positive part of $\log|w-z|$ is always integrable, so the content of the printed "$\int\log|w-z|\,d\mu(w)<\infty$" is integrability of the negative part; it is stated as $\mu$-integrability, since a Bochner integral is finite by definition.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, pp. 2054–2055 (PDF 32–33), §8, proof of Theorem 1.15, (8.1)

import Mathlib
import Definitions.Def_UnivESD_LogDet_Basic

open MeasureTheory

namespace UnivESD.LogDet

/-- (8.1), Tao–Vu, Ann. Probab. 38 (2010), §8, pp. 2054–2055. For a probability measure `μ` on `ℂ`
with `∫ |w|² dμ(w) < ∞`, the function `z ↦ ∫ |log|w − z|| dμ(w)` is locally integrable (its
lower Lebesgue integral over every compact set is finite), and for Lebesgue-almost every `z` the
function `w ↦ log|w − z|` is `μ`-integrable, so that `∫ log|w − z| dμ(w)` is finite. -/
theorem eq_8_1 (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun w : ℂ => ‖w‖ ^ 2) μ) :
    (∀ K : Set ℂ, IsCompact K →
      ∫⁻ z in K, ∫⁻ w, ENNReal.ofReal |Real.log ‖w - z‖| ∂μ < ⊤) ∧
    ∀ᵐ z ∂(volume : Measure ℂ), Integrable (fun w : ℂ => Real.log ‖w - z‖) μ := by sorry

end UnivESD.LogDet
