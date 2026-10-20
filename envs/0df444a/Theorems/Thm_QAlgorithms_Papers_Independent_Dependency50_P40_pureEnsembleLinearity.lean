-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_pureEnsembleLinearity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.pureEnsembleLinearity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:17:31.02901+00:00
-- url     : https://prove2.me/theorems/1b9fcf99-e21b-451a-a72e-aa1db235b6d6
-- title:
--   Pure-state discrete ensemble fidelity is affine in the channel
-- statement:
--   Let $H=\mathbb C^h$, $h>0$, and let $(p_i,|\psi_i\rangle)_{i\in I}$ be a discrete ensemble with arbitrary index type $I$, $p_i\ge0$, summable weights, $\sum_i p_i=1$, and $\|\psi_i\|=1$. Write $F$ for the root fidelity in (1), $\rho_i=|\psi_i\rangle\langle\psi_i|$, and $\overline F(p,\psi,\mathcal B)=\sum_i p_i F(\rho_i,\mathcal B(\rho_i))^2$. For CPTP endomorphisms $\mathcal B,\mathcal C$ and $0\le t\le1$, their mixture is CPTP, all three weighted score series are summable, and
--
--   $$
--   \overline F(p,\psi,t\mathcal B+(1-t)\mathcal C)
--   =t\overline F(p,\psi,\mathcal B)+(1-t)\overline F(p,\psi,\mathcal C).
--   $$
--
--   Thus ensemble squared fidelity is a linear objective on the convex set of channels when each component is pure. No analogous assertion for mixed components is made.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 2, II, following Eq. (4): pure-state ensemble fidelity is linear in the channel

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.2, (4) and following sentence: discrete pure-ensemble fidelity is affine in a channel. -/
theorem pureEnsembleLinearity {I : Type*} {h : ℕ} (hh : 0 < h)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (hmass : ∑' i, p i = 1)
    (psi : I → EuclideanSpace ℂ (Fin h)) (hpsi : ∀ i, IsState (psi i))
    (B C : Superop (Fin h) (Fin h)) (hB : IsChannel B) (hC : IsChannel C)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Summable (fun i => p i * rootFidelity (pureDensity (psi i)) (B (pureDensity (psi i))) ^ 2) ∧
    Summable (fun i => p i * rootFidelity (pureDensity (psi i)) (C (pureDensity (psi i))) ^ 2) ∧
    Summable (fun i => p i * rootFidelity (pureDensity (psi i))
      (channelMix t B C (pureDensity (psi i))) ^ 2) ∧
    IsChannel (channelMix t B C) ∧
    ensembleFidelity p psi (channelMix t B C) =
      t * ensembleFidelity p psi B + (1 - t) * ensembleFidelity p psi C := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
