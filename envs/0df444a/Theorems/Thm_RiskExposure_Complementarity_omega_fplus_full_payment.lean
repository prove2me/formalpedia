-- Prove2me | Theorems.Thm_RiskExposure_Complementarity_omega_fplus_full_payment
-- name    : RiskExposure.Complementarity.omega_fplus_full_payment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:56.123201+00:00
-- url     : https://prove2.me/theorems/60afb6fd-a3f3-4bd4-a10c-16299f7fd31f
-- title:
--   Internet Appendix p. 9 — on Ω^{f+}_{−i}: d*_i(ω^{i=f}) = d̄_i and Σ_j θ_ij d*_j(ω^{i=f}) = Σ_j θ_ij d*_j(ω^{i=s})
-- statement:
--   In the setting of the mission, let $Z\in[\underline Z,\overline Z]^N$, let $i$ be a bank and let $\omega$ be a state in which bank $i$'s project fails ($\omega=\omega^{i=f}$). Suppose $\omega_{-i}\in\Omega^{f+}_{-i}$, i.e.
--   $$\sum_j\theta_{ij}d_j^*(\omega^{i=f})-d_i^*(\omega^{i=f})-v_i>0 .$$
--   Then
--   $$d_i^*(\omega^{i=f})=\bar d_i\qquad\text{and}\qquad\sum_j\theta_{ij}d_j^*(\omega^{i=f})=\sum_j\theta_{ij}d_j^*(\omega^{i=s}).$$
--
--   A bank that survives its own failure pays its interbank debt in full, and its project outcome is then irrelevant to what it receives from the network. This is what removes the states of $\Omega^{f+}_{-i}$ from the risk-taking distortion in non-regular networks.
--
--   **Formalization Note** $d^*$ is the greatest payment equilibrium; the second identity is stated for the weighted sum of receipts, as on the page.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 9, second paragraph (claims following the definition of Ω^{f+}_{−i}, p. 8)

import Mathlib
import Definitions.Def_RiskExposure_Complementarity_Model

namespace RiskExposure.Complementarity

theorem omega_fplus_full_payment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi) (ω : ι → Bool) (i : ι) (hω : ω i = false)
    (hfp : 0 < ∑ j, theta dbar i j * paymentEq dbar v ω Z j - paymentEq dbar v ω Z i - v i) :
    paymentEq dbar v ω Z i = dbarTot dbar i ∧
      ∑ j, theta dbar i j * paymentEq dbar v ω Z j =
        ∑ j, theta dbar i j * paymentEq dbar v (Function.update ω i true) Z j := by sorry

end RiskExposure.Complementarity
