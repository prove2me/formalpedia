-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P89_loss_protection_ceiling
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P89.loss_protection_ceiling
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:30:30.655498+00:00
-- url     : https://prove2.me/theorems/c22b68e9-9cf2-4b48-91f7-9701b6015517
-- title:
--   Positive chip loss imposes a finite usable protection depth
-- statement:
--   In the source's independent-loss construction, let $\eta_s,\eta_d,\eta_c\in(0,1]$, $\alpha>0$, $\beta,\tau_s,\tau_f\ge0$ and $c_{\rm ch},c_f>0$, with consistent units. Assume positive attenuation during a chip feedforward step, $\beta\tau_s>0$. Put $a=e^{-\beta\tau_s c_{\rm ch}}$, $f=e^{-\alpha\tau_f c_f}$, $h=\eta_s\eta_d/(2-\eta_s\eta_d)$. For a fusion depth $k$, node count $n\ge1$ and range $L\ge0$, the traveling and retained photon survival probabilities are
--
--   $$s_{\rm trav}=e^{-\alpha L/(2n)}a^{k+2}h\eta_c,\qquad s_{\rm stat}=e^{-\alpha L/n}a^{k+2}fh\eta_c.$$
--
--   There is an integer $K$, depending only on the devices, such that
--
--   $$\forall k\ge K\;\forall n\ge1\;\forall L\ge0,\qquad s_{\rm trav}<\tfrac12\quad\text{and}\quad s_{\rm stat}<\tfrac12.$$
--
--   Thus this construction eventually leaves the tree code's operating regime as protection depth grows. This is the mechanism used by the source's finite-protection discussion; it does not assert that clusters cannot be created or that arbitrary optical computing is impossible. Positive per-step chip attenuation is essential; the allowed zero-delay or zero-attenuation boundary is excluded here.
-- source:
--   Rate-distance tradeoff and resource costs for all-optical quantum repeaters, arXiv:1603.01353v4, PDF p. 14, V: finite usable protection depth under on-chip loss

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

namespace QAlgorithms.Papers.Independent.Intakenext100.P89

open scoped BigOperators ComplexConjugate

-- Accepted probability primitives: symbol true is success; choose n x is zero for x > n.

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

/-- Source p.14: positive loss per chip feedforward step eventually puts photon survival
below the tree code's 1/2 operating threshold, uniformly over range and node count.
Zero per-step attenuation is excluded. This bounds usable protection in this construction;
it does not assert physical noncreation or an impossibility for arbitrary optical computing. -/
theorem loss_protection_ceiling (d : Devices) (hLoss : 0 < d.beta * d.tauS) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (n : ℕ), 0 < n → ∀ (L : ℝ), 0 ≤ L →
      travelingSurvival d k n L < (1 : ℝ) / 2 ∧
      stationarySurvival d k n L < (1 : ℝ) / 2 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P89
