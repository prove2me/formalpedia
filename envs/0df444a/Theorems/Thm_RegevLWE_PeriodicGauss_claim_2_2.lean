-- Prove2me | Theorems.Thm_RegevLWE_PeriodicGauss_claim_2_2
-- name    : RegevLWE.PeriodicGauss.claim_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:34.281475+00:00
-- url     : https://prove2.me/theorems/5964c5de-0d1e-4772-9a76-6c0443e73019
-- title:
--   Claim 2.2 — for 0 < α < β ≤ 2α, Δ(Ψ_α, Ψ_β) ≤ 9(β/α − 1)
-- statement:
--   For $\beta > 0$ let $\Psi_\beta$ be the periodic normal density on $\mathbb{T} = [0,1)$,
--   $$\Psi_\beta(r) = \sum_{k=-\infty}^{\infty} \frac{1}{\beta}\exp\Bigl(-\pi\Bigl(\frac{r-k}{\beta}\Bigr)^2\Bigr),$$
--   the law of a normal variable with mean $0$ and standard deviation $\beta/\sqrt{2\pi}$ reduced modulo $1$, and let $\Delta(\varphi_1,\varphi_2) = \int_0^1 |\varphi_1(r) - \varphi_2(r)|\,dr$ be the statistical distance on $\mathbb{T}$ (no factor $\tfrac12$). Then for any $0 < \alpha < \beta \le 2\alpha$,
--   $$\Delta(\Psi_\alpha, \Psi_\beta) \le 9\Bigl(\frac{\beta}{\alpha} - 1\Bigr).$$
--
--   The claim says that a small relative change of the parameter $\beta$ changes the distribution $\Psi_\beta$, the error distribution of the Learning with Errors problem, only slightly.
--
--   **Formalization Note** $\Delta$ is the lower Lebesgue integral over `Set.Ico 0 1` with values in $[0,\infty]$ (`statDistT`), so it cannot vanish on a non-integrable difference; the right-hand side is compared through `ENNReal.ofReal`. No hypothesis is added to the printed ones.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:16, Claim 2.2

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian

open MeasureTheory

namespace RegevLWE.PeriodicGauss

/-- **Claim 2.2** (Regev, J. ACM 2009, p. 34:16). For any `0 < α < β ≤ 2α`, the periodic normal
densities on `𝕋 = [0, 1)` satisfy `Δ(Ψ_α, Ψ_β) ≤ 9 (β/α - 1)`. -/
theorem claim_2_2 (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β ≤ 2 * α) :
    statDistT (Psi α) (Psi β) ≤ ENNReal.ofReal (9 * (β / α - 1)) := by sorry

end RegevLWE.PeriodicGauss
