-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_chaotic_inflation_estimates_sec_3_1
-- name    : PereiraGuimaraesElko.chaotic_inflation_estimates_sec_3_1
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:52:20.19859+00:00
-- url     : https://prove2.me/theorems/aaa9703f-d8c7-4b60-8f3d-1d4c9d5af21a
-- title:
--   Eq. (3.6) and Sec. 3.1: initial Hubble rate, $V(\Phi_i)$, slow-roll parameters, mass and coupling for the benchmark parameters
-- statement:
--   Work in Planck units $m_{\rm pl}=1$, so $\kappa^2=8\pi$. Take the benchmark parameters of Section 3.1:
--   $$v_0=0,\qquad \Phi_i=2.1,\qquad \sigma=1,\qquad \Lambda=5\times10^{-6},$$
--   the potential $V(\Phi)=v_0+\Lambda^4(1-\Phi^2/\sigma^2)^2$ of (3.1), and the slow-roll value of the initial Hubble rate (3.6),
--   $$H^2(t_i)=\frac{\kappa^2}{3}\left(1+\frac{\kappa^2\Phi_i^2}{8}\right)V(\Phi_i).$$
--   Then each of the following quantities agrees with the value printed in the paper to within $5\%$ relative error:
--
--   1. $H^2(t_i)\simeq9.04\times10^{-19}$;
--   2. $t_i=H(t_i)^{-1}\simeq5.7\times10^{-35}\,$s, using $m_{\rm pl}=1.86\times10^{43}\,{\rm s}^{-1}$;
--   3. $V(\Phi_i)\simeq7.2\times10^{-21}$;
--   4. $\epsilon=\dfrac1{\kappa^2}\left(\dfrac{V'(\Phi_i)}{V(\Phi_i)}\right)^2\simeq0.24$ (slow-roll parameter (1.6));
--   5. $|\eta|=\left|\dfrac1{\kappa^2}\dfrac{V''(\Phi_i)}{(1+\kappa^2\Phi_i^2/8)V(\Phi_i)}\right|\simeq0.011$ (slow-roll parameter (3.5));
--   6. $m=\sqrt2\,\mu=\sqrt2\cdot2\Lambda^2/\sigma\simeq7.1\times10^{-11}$;
--   7. $m\simeq8.6\times10^{8}\,$GeV, using $m_{\rm pl}=1.22\times10^{19}\,$GeV;
--
--   and the self-coupling is exactly $\alpha=4\Lambda^4/\sigma^4=2.5\times10^{-21}$.
--
--   These are the analytic estimates that fix the benchmark model before the numerical integration.
--
--   **Formalization Note** The paper writes "$\simeq$" with two or three significant digits (and truncates $V(\Phi_i)=7.27\ldots\times10^{-21}$ to $7.2$); a uniform $5\%$ relative tolerance is used to encode "$\simeq$". The e-fold number $N=93$ and the other outputs of the numerical integration are not part of this item.
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), pp. 7–8, Sec. 3.1, Eq. (3.6), slow-roll parameters (1.6) and (3.5), and the following values; unit conversions m_pl = 1.22e19 GeV = 1.86e43 s^-1 from Appendix B, p. 15

import Mathlib

namespace PereiraGuimaraesElko

theorem chaotic_inflation_estimates_sec_3_1 (κ Λ σ v₀ Φi Hi2 : ℝ) (V : ℝ → ℝ)
    (hκ : κ ^ 2 = 8 * Real.pi)
    (hΛ : Λ = 5e-6) (hσ : σ = 1) (hv₀ : v₀ = 0) (hΦi : Φi = 2.1)
    (hV : ∀ Φ, V Φ = v₀ + Λ ^ 4 * (1 - Φ ^ 2 / σ ^ 2) ^ 2)
    (hHi2 : Hi2 = κ ^ 2 / 3 * (1 + κ ^ 2 * Φi ^ 2 / 8) * V Φi) :
    |Hi2 - 9.04e-19| ≤ 0.05 * 9.04e-19 ∧
    |1 / (Real.sqrt Hi2 * 1.86e43) - 5.7e-35| ≤ 0.05 * 5.7e-35 ∧
    |V Φi - 7.2e-21| ≤ 0.05 * 7.2e-21 ∧
    |1 / κ ^ 2 * (deriv V Φi / V Φi) ^ 2 - 0.24| ≤ 0.05 * 0.24 ∧
    |abs (1 / κ ^ 2 * deriv (deriv V) Φi / ((1 + κ ^ 2 * Φi ^ 2 / 8) * V Φi)) - 0.011|
      ≤ 0.05 * 0.011 ∧
    |Real.sqrt 2 * (2 * Λ ^ 2 / σ) - 7.1e-11| ≤ 0.05 * 7.1e-11 ∧
    |Real.sqrt 2 * (2 * Λ ^ 2 / σ) * 1.22e19 - 8.6e8| ≤ 0.05 * 8.6e8 ∧
    4 * Λ ^ 4 / σ ^ 4 = 2.5e-21 := by
  sorry

end PereiraGuimaraesElko
