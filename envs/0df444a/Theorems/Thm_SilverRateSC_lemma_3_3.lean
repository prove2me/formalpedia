-- Prove2me | Theorems.Thm_SilverRateSC_lemma_3_3
-- name    : SilverRateSC.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:48:02.40523+00:00
-- url     : https://prove2.me/theorems/127bf34d-a043-4553-a518-a25f8d0f6c37
-- title:
--   Lemma 3.3 — bridging: $D_{i+1}/D_i\ge\frac14\eta_i\frac{b_i-4}{s_i+2}$, and the bridge follows the repair trajectory
-- statement:
--   Work in the local setting of §3: $\ell_i\ge0$, $D_i>0$, nonnegative gap stepsizes with sum $s_i$, and $\eta_i$ from (7). Let $\kappa\ge4$, $s_i/\kappa\le1/16$ and $\eta_i>0$. The bridging component $\Phi_i$ (with $\ell_{i+1}=D_i\eta_i/2$) is nonnegative, convex and $1$-smooth, with $\partial_Y\Phi_i\le0$ everywhere and $\Phi_i(X,Y)=0$ whenever $X\le\ell_i$, $Y\ge0$; moreover $\partial_Y\Phi_i(X,Y)=0$ for all $X\in\mathbb R$, $Y\ge\ell_{i+1}$. For every $b_i>4$ and every sequence $f_j\ge0$, the iterations (9) satisfy (8), and
--   $$\frac{D_{i+1}}{D_i}\ge\frac14\eta_i\frac{b_i-4}{s_i+2},\qquad \frac{\ell_{i+1}}{D_{i+1}}\le2\,\frac{s_i+2}{b_i-4}.$$
--   With the same $\ell_i$, $D_i$, stepsizes and sequence $f_j\ge0$, the bridge and the Huber repair component follow the same trajectory through the checkpoint update.
--
--   The bridge lets a bending component, which needs $f_j=0$, follow a repair component.
--
--   Differences from the source:
--   - encoding: standing setup of §3 (p.13): input threshold ℓ_i ≥ 0, incoming excess D_i > 0, gap stepsizes h_j ≥ 0 → explicit hypotheses hℓ, hD, hh; reason: standing assumptions of the section, stated once on p.13
--   - encoding: D_{i+1} determined by Y_{m_gap+1} = ℓ_{i+1} + D_{i+1} → outExcess κ Φ hs b ℓ D ℓ' f, and (8) is IsTransfer; reason: D_{i+1} is not a free quantity; the predicate is (8) verbatim
--   - encoding: every sequence f_j ≥ 0 → every f : ℕ → ℝ with f j ≥ 0 for all j; reason: only f_1, …, f_{m_gap+1} enter (9); any nonnegative finite sequence extends
--   - encoding: functions on ℝ², ∂_Y, 1-smooth, Π_K → EuclideanSpace ℝ (Fin 2), coordinate 1 of gradient, KatyushaNs.IsConvexLSmooth 1, OrabonaOL.OGD.IsEuclideanProj; reason: Lean representation; same objects
--   - reading: the same trajectory through the checkpoint update, with the same stepsizes and f_j ≥ 0 (no range for b_i stated in that sentence) → equality of the two sequences (9) at every step 0 ≤ j ≤ m_gap + 1, for every checkpoint stepsize b ∈ ℝ and every f ≥ 0; reason: the sentence names no range for b; the points before the checkpoint update do not involve b, so the stronger reading is taken
--   - encoding: gap stepsizes h_1, …, h_{m_gap}, their sum s_i, χ_i, η_i, the standing h_j < κ → hs : List ℝ, s_i = hs.sum, chiGap, etaGap; no separate hypothesis h_j < κ; reason: same data; h_j ≥ 0 and s_i/κ ≤ 1/16 imply h_j ≤ κ/16 < κ
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma 3.3, p.16; construction §3.3, p.16; setting §3, p.13

import Mathlib
import Definitions.Def_SilverRateSC_bridgePhi
import Definitions.Def_SilverRateSC_IsTransfer
import Definitions.Def_SilverRateSC_IsLocalComponent

namespace SilverRateSC

/-- **Lemma 3.3 (Bridging).** Let `κ ≥ 4`, `s_i/κ ≤ 1/16`, and `η_i > 0`. The bridging function
`Φ_i` is nonnegative, convex and `1`-smooth, with `∂_YΦ_i ≤ 0` everywhere and `Φ_i(X, Y) = 0`
whenever `X ≤ ℓ_i`, `Y ≥ 0`. Moreover, `∂_YΦ_i(X, Y) = 0` for all `X ∈ ℝ`, `Y ≥ ℓ_{i+1}`. For
every `b_i > 4` and every sequence `f_j ≥ 0`, the iterations (9) satisfy (8), and
`D_{i+1}/D_i ≥ (1/4) η_i (b_i − 4)/(s_i + 2)`, `ℓ_{i+1}/D_{i+1} ≤ 2(s_i + 2)/(b_i − 4)`. With the
same `ℓ_i, D_i`, stepsizes and sequence `f_j ≥ 0`, the bridge and the Huber repair component of
§3.2 follow the same trajectory through the checkpoint update.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma 3.3, p. 16 (construction §3.3, p. 16; setting of §3, pp. 13–14).

**Formalization Note** `Φ_i = bridgePhi κ hs ℓ D`, `ℓ_{i+1} = bridgeEll κ hs ℓ D = D_i η_i/2`,
`D_{i+1} = outExcess …`; `ℓ_i ≥ 0`, `D_i > 0` and `h_j ≥ 0` are the setting of §3 (`h_j < κ`
follows from `s_i/κ ≤ 1/16`). The last sentence is the equality of the two trajectories (9) at
every step `0 ≤ j ≤ m_gap + 1`; it is stated for every checkpoint stepsize `b`, every sequence
`f ≥ 0`. -/
theorem lemma_3_3 (κ ℓ D : ℝ) (hs : List ℝ) (hκ : 4 ≤ κ) (hℓ : 0 ≤ ℓ) (hD : 0 < D)
    (hh : ∀ h ∈ hs, 0 ≤ h) (hsκ : hs.sum / κ ≤ 1 / 16) (hη : 0 < etaGap κ hs ℓ D) :
    IsLocalComponent (bridgePhi κ hs ℓ D) ℓ ∧ IsFlatAbove (bridgePhi κ hs ℓ D) (bridgeEll κ hs ℓ D) ∧
      (∀ b : ℝ, 4 < b → ∀ f : ℕ → ℝ, (∀ j, 0 ≤ f j) →
        IsTransfer κ (bridgePhi κ hs ℓ D) hs b ℓ D (bridgeEll κ hs ℓ D) f ∧
        1 / 4 * etaGap κ hs ℓ D * ((b - 4) / (hs.sum + 2)) ≤
          outExcess κ (bridgePhi κ hs ℓ D) hs b ℓ D (bridgeEll κ hs ℓ D) f / D ∧
        bridgeEll κ hs ℓ D / outExcess κ (bridgePhi κ hs ℓ D) hs b ℓ D (bridgeEll κ hs ℓ D) f ≤
          2 * (hs.sum + 2) / (b - 4)) ∧
      ∀ b : ℝ, ∀ f : ℕ → ℝ, (∀ j, 0 ≤ f j) → ∀ j ≤ hs.length + 1,
        localIter κ (bridgePhi κ hs ℓ D) (hs ++ [b]) f !₂[ℓ + D, 0] j =
          localIter κ (repairPhi κ hs ℓ D) (hs ++ [b]) f !₂[ℓ + D, 0] j := by sorry

end SilverRateSC
