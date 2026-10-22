-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_networkOptimum
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.networkOptimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:47:18.154903+00:00
-- url     : https://prove2.me/theorems/ebeaa35a-a451-4be6-a4aa-3eb380d67dfe
-- title:
--   VII.C: continuous linear-network toy cost and optimal link length, Eqs.(79)–(80)
-- statement:
--   In the continuous linear-network toy model, let $C_1,L,K_{\rm target},a,k,\alpha>0$. Arbitrarily parallel devices and trusted stations with neglected station costs give the continuous device count $N=(L/\ell)K_{\rm target}/K(\ell)$, with $K(\ell)=a10^{-k\alpha\ell/10}$. For $\ell>0$,
--
--   $$C_{\rm tot}(\ell)={C_1LK_{\rm target}\over\ell K(\ell)},\qquad \ell_*={10\over k\alpha\ln10}.$$
--
--   The function $\ell K(\ell)$ has its unique maximum over positive lengths at $\ell_*$, which minimizes cost. If a finite chain requires $\ell\le L$, the constrained maximizer is $\min\{L,\ell_*\}$. No integer rounding, station cost, or discrete network-design optimality is asserted.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 40, VII.C: continuous linear-network toy cost and optimal link length, Eqs.(79)–(80)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(79)–(80), PDF p.40: continuous device-count relaxation, including the
unique unconstrained optimum and the finite-chain constrained optimizer. -/
theorem networkOptimum (C L target a k alpha : ℝ) (hC : 0 < C) (hL : 0 < L)
    (htarget : 0 < target) (ha : 0 < a) (hk : 0 < k) (halpha : 0 < alpha) :
    let K := fun ell : ℝ => a*Real.rpow 10 (-k*alpha*ell/10)
    let opt := 10/(k*alpha*Real.log 10)
    0 < opt ∧
    (∀ ell : ℝ, 0 < ell → networkCost C L target ell (K ell) = C*L*target/(ell*K ell)) ∧
    (∀ ell : ℝ, 0 < ell → ell*K ell ≤ opt*K opt ∧
      (ell*K ell = opt*K opt ↔ ell = opt) ∧
      networkCost C L target opt (K opt) ≤ networkCost C L target ell (K ell)) ∧
    (∀ ell : ℝ, 0 < ell → ell ≤ L → ell*K ell ≤ min L opt*K (min L opt)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
