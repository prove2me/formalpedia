-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothed_zero_sum_65000_of_sine_weight
-- name    : TaoFivePrimes.smoothed_zero_sum_65000_of_sine_weight
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:55:29.729591+00:00
-- url     : https://prove2.me/theorems/adb91e0b-2311-4d57-84c8-03cbca0023c3
-- title:
--   Smoothed zero-sum bound from a sine-sensitive high-zero weight
-- statement:
--   Suppose that all nontrivial zeta zeros with ordinate between $0$ and $65000$ lie on the critical line. Let $a\ge1$, $h>0$, $2h\le a$, $z\ge a+2h$, $B\ge0$, and put $r=h/(a+h)$. For a zero $\rho=\beta+i\gamma$, define
--
--   $$
--   W_r(\rho)=\frac{\min\{4\sin^2(\gamma r/2)+8r+3|\gamma|r^2,\,4\}}{|\gamma|^3}.
--   $$
--
--   Assume that every finite set $Z$ of nontrivial zeros with $|\operatorname{Im}\rho|>65000$ satisfies $\sum_{\rho\in Z}m_\rho W_r(\rho)\le B$, where $m_\rho$ is the analytic multiplicity. Then, for the published double-box zero kernel $K$,
--
--   $$
--   \sum_{\rho}\left|m_\rho K(a,h,\rho)\right|
--   \le \frac{301}{10}\sqrt z+\frac{z^{23/8}}{h^2}B.
--   $$
--
--   The sum runs over all nontrivial zeros of both signs. The displayed high-zero weight assumption is explicit; this theorem does not assert finite-height RH or the numerical weight bound.
-- source:
--   Derived from the proved Dusart double-box zero kernel bounds, the proved 65,000 low-zero reciprocal-weight bound, and the proved 7/8 zero-free region. The sine-sensitive weight is an explicit additional hypothesis.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic
open DusartSmoothing Complex Set

theorem TaoFivePrimes.smoothed_zero_sum_65000_of_sine_weight (a h z B : ℝ) (ha : 1 ≤ a) (hh : 0 < h) (hsmall : 2*h ≤ a)
    (haz : a+2*h ≤ z) (hB : 0 ≤ B)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 65000 → s.re = 1/2)
    (hweight : ∀ Z : Finset ℂ, (∀ ρ ∈ Z, RvM.IsNontrivialZero ρ) →
      (∀ ρ ∈ Z, 65000 < |ρ.im|) →
      (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
        ((min (4*(Real.sin (ρ.im*(h/(a+h))/2))^2 + 8*(h/(a+h)) +
          3 * |ρ.im| * (h/(a+h))^2) 4) / |ρ.im|^3)) ≤ B) :
    (∑' ρ : NontrivialZetaZero,
      ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      (301/10:ℝ)*Real.sqrt z + (z^(23/8:ℝ)/h^2)*B := by sorry
