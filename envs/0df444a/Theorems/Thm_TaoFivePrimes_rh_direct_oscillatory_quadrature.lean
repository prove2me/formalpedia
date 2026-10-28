-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_oscillatory_quadrature
-- name    : TaoFivePrimes.rh_direct_oscillatory_quadrature
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:27:40.129997+00:00
-- url     : https://prove2.me/theorems/b7809641-e17d-4b14-bc65-6e3083c8d57c
-- title:
--   Direct oscillatory theta quadrature with exact Taylor panels
-- statement:
--   Let $I_{\tau,k}$ be the oscillatory theta integral and $Q_{\tau,k}$ its sixteen-panel, 184-term exact Taylor quadrature sum, as defined in the accompanying quadrature model. For every integer $k\ge0$ and real $|\tau|\le100$,
--
--   $$
--   \left|I_{\tau,k}-Q_{\tau,k}\right|\le \frac{17}{10^{82}}.
--   $$
--
--   The panel coefficients are exact derivatives of the analytic kernel. A numerical evaluation of those derivatives and a zero-location result require separate certificates.
-- source:
--   Direct oscillatory extension of the theta/Mellin framework due to Gabewhigham and the 16-panel, 184-jet quadrature framework due to sometik179.

import Definitions.Def_TaoFivePrimes_RHDirectOscillatoryQuadrature

theorem TaoFivePrimes.rh_direct_oscillatory_quadrature (τ : ℝ) (hτ : |τ|≤100) (k : ℕ) :
    ‖RHDirectOscillatory.rawIntegral τ k - RHDirectOscillatory.panelSum τ k‖
      ≤ 17/10^82 := by sorry
