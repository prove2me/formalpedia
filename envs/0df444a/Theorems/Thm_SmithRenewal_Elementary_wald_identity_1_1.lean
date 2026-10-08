-- Prove2me | Theorems.Thm_SmithRenewal_Elementary_wald_identity_1_1
-- name    : SmithRenewal.Elementary.wald_identity_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:29:57.248352+00:00
-- url     : https://prove2.me/theorems/e990c8ad-6110-4b87-a5c3-b1b0be6b7562
-- title:
--   §1.2, (1.1), p. 246 — t + Eζ_t = μ₁{1 + H(t)} for μ₁ < ∞
-- statement:
--   Let $(X_i)$ be a renewal process with finite mean lifetime $\mu_1 = \mathbb E X_i < \infty$, renewal function $H(t) = \mathbb E N_t$, and residual lifetime $\zeta_t$ defined by $S_{N_t+1} = t + \zeta_t$. Then for every $t \ge 0$,
--   $$t + \mathbb E\zeta_t = \mu_1\{1 + H(t)\}. \tag{1.1}$$
--
--   Equation (1.1) is Wald's identity for the stopping index $N_t + 1$. It is the key relation behind both halves of the elementary renewal theorem: since $\zeta_t \ge 0$ it gives $\mu_1\{1+H(t)\} \ge t$, and for a bounded lifetime it gives $\mu_1\{1+H(t)\} \le t + \Delta$.
--
--   **Formalization Note** All three expectations are lower integrals in $[0,\infty]$; the identity is asserted in $[0,\infty]$, so it also asserts that $\mathbb E\zeta_t$ is finite exactly when $H(t)$ is. Times are $t \ge 0$.
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §1.2, p. 246, (1.1)

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- Equation (1.1) (Smith, *Renewal Theory and Its Ramifications*, J. R. Statist. Soc. B 20(2):243–283 (1958), §1.2, p. 246, (1.1)): if `μ₁ < ∞` then, with
`S_{N_t+1} = t + ζ_t`, "t + Eζ_t = μ₁{1 + H(t)}".

Formalization Note: `t ≥ 0` is a time on the paper's half-line (for `t < 0` the identity fails
under the `ofReal` reading). `Eζ_t`, `H(t)` and `μ₁` are lower integrals in `[0, ∞]`;
`ζ_t > 0` wherever `N_t < ∞`, so `ENNReal.ofReal` does not truncate it except on a null set. -/
theorem wald_identity_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X)
    (hmu : mu1 X P < ⊤) (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal t + ∫⁻ ω, ENNReal.ofReal (zeta X t ω) ∂P = mu1 X P * (1 + H X P t) := by sorry

end SmithRenewal.Elementary
