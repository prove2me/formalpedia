-- Prove2me | Theorems.Thm_SilverRateSC_lemma_3_2
-- name    : SilverRateSC.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:46:57.918298+00:00
-- url     : https://prove2.me/theorems/60c1681c-aec0-4bef-aacf-a239102d0499
-- title:
--   Lemma 3.2 — Huber repair: exact transfer ratio and relative threshold (14)
-- statement:
--   Work in the local setting of §3: $\ell_i\ge0$, $D_i>0$, gap stepsizes $0\le h_j<\kappa$, and $\chi_i,\eta_i$ from (7). Let $\kappa>1$ and $\eta_i>0$. The Huber repair component $\Phi_i$ of (13) is nonnegative, convex and $1$-smooth, with $\partial_Y\Phi_i\le0$ everywhere and $\Phi_i(X,Y)=0$ whenever $X\le\ell_i$, $Y\ge0$. For every $b_i>0$ and every sequence $f_j\ge0$, the iterations (9) satisfy (8) with $\ell_{i+1}=(\kappa-1)(1-\chi_i)\delta_{\rm H}/2$, and
--   $$\frac{D_{i+1}}{D_i}=\frac{(1-1/\kappa)b_i\chi_i\eta_i}{2[2+(\kappa-1)(1-\chi_i)]},\qquad \frac{\ell_{i+1}}{D_{i+1}}=\frac{\kappa(1-\chi_i)}{b_i\chi_i}.$$
--
--   The repair component restores a bounded relative threshold after long unselected gaps, whatever the preceding component contributes.
--
--   Differences from the source:
--   - encoding: standing setup of §3 (p.13): ℓ_i ≥ 0, D_i > 0, gap stepsizes 0 ≤ h_j < κ → explicit hypotheses hℓ, hD, hh (∀ h ∈ hs, 0 ≤ h ∧ h < κ); reason: standing assumptions of the section, stated once on p.13; the lemma lists only κ > 1 and η_i > 0
--   - encoding: D_{i+1} determined by Y_{m_gap+1} = ℓ_{i+1} + D_{i+1} → outExcess κ Φ hs b ℓ D ℓ' f, and (8) is IsTransfer; reason: D_{i+1} is not a free quantity; the predicate is (8) verbatim
--   - encoding: every sequence f_j ≥ 0 → every f : ℕ → ℝ with f j ≥ 0 for all j; reason: only f_1, …, f_{m_gap+1} enter (9); any nonnegative finite sequence extends
--   - encoding: functions on ℝ², ∂_Y, 1-smooth, Π_K → EuclideanSpace ℝ (Fin 2), coordinate 1 of gradient, KatyushaNs.IsConvexLSmooth 1, OrabonaOL.OGD.IsEuclideanProj; reason: Lean representation; same objects
--   - encoding: gap stepsizes h_1, …, h_{m_gap}, χ_i, η_i → hs : List ℝ, chiGap, etaGap; reason: same data
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma 3.2, p.16; construction (13), p.15; setting §3, p.13

import Mathlib
import Definitions.Def_SilverRateSC_repairPhi
import Definitions.Def_SilverRateSC_IsTransfer
import Definitions.Def_SilverRateSC_IsLocalComponent

namespace SilverRateSC

/-- **Lemma 3.2 (Repairing).** Let `κ > 1` and `η_i > 0`. The function `Φ_i` defined in (13) is
nonnegative, convex and `1`-smooth, with `∂_YΦ_i ≤ 0` everywhere and `Φ_i(X, Y) = 0` whenever
`X ≤ ℓ_i`, `Y ≥ 0`. For every `b_i > 0` and every sequence `f_j ≥ 0`, the iterations (9) satisfy
(8), and `D_{i+1}/D_i = (1 − 1/κ) b_i χ_i η_i / (2[2 + (κ − 1)(1 − χ_i)])`,
`ℓ_{i+1}/D_{i+1} = κ(1 − χ_i)/(b_i χ_i)` (14).

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma 3.2, p. 16 (construction (13), p. 15; setting of §3, pp. 13–14).

**Formalization Note** The setting of §3 (p. 13) is explicit: `ℓ_i ≥ 0`, `D_i > 0` and gap
stepsizes `0 ≤ h_j < κ`. `Φ_i = repairPhi κ hs ℓ D`, `ℓ_{i+1} = repairEll κ hs ℓ D`
`= (κ − 1)(1 − χ_i)δ_H/2`, `D_{i+1} = outExcess …`. A sequence `f_j ≥ 0` is `f : ℕ → ℝ`
nonnegative (only `f_1, …, f_{m_gap+1}` are read). -/
theorem lemma_3_2 (κ ℓ D : ℝ) (hs : List ℝ) (hκ : 1 < κ) (hℓ : 0 ≤ ℓ) (hD : 0 < D)
    (hh : ∀ h ∈ hs, 0 ≤ h ∧ h < κ) (hη : 0 < etaGap κ hs ℓ D) :
    IsLocalComponent (repairPhi κ hs ℓ D) ℓ ∧
      ∀ b : ℝ, 0 < b → ∀ f : ℕ → ℝ, (∀ j, 0 ≤ f j) →
        IsTransfer κ (repairPhi κ hs ℓ D) hs b ℓ D (repairEll κ hs ℓ D) f ∧
        outExcess κ (repairPhi κ hs ℓ D) hs b ℓ D (repairEll κ hs ℓ D) f / D =
          (1 - 1 / κ) * b * chiGap κ hs * etaGap κ hs ℓ D /
            (2 * (2 + (κ - 1) * (1 - chiGap κ hs))) ∧
        repairEll κ hs ℓ D / outExcess κ (repairPhi κ hs ℓ D) hs b ℓ D (repairEll κ hs ℓ D) f =
          κ * (1 - chiGap κ hs) / (b * chiGap κ hs) := by sorry

end SilverRateSC
