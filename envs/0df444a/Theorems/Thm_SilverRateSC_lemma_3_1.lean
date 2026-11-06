-- Prove2me | Theorems.Thm_SilverRateSC_lemma_3_1
-- name    : SilverRateSC.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:47:12.845193+00:00
-- url     : https://prove2.me/theorems/d016566d-4ac4-401c-97cb-64a31205424d
-- title:
--   Lemma 3.1 — bending: $D_{i+1}/D_i\ge\frac{b_i-8}{c_\beta(a_\beta+s_i+8)}\eta_i(1-s_i/\kappa)$
-- statement:
--   Work in the local setting of §3: an input threshold $\ell_i\ge0$, an incoming excess $D_i>0$, nonnegative gap stepsizes $h_1,\dots,h_{m_{\rm gap}}$ with sum $s_i$, and $\eta_i$ from (7). Let $\kappa\ge4$, $0<\beta\le1/4$, $s_i/\kappa\le1/16$ and $\eta_i>0$.
--
--   There exist a nonnegative convex $1$-smooth local hard function $\Phi_i$ and a threshold $\ell_{i+1}\ge0$, **independent of the checkpoint stepsize $b_i$**, such that $\partial_Y\Phi_i\le0$ everywhere,
--   $$\Phi_i(X,Y)=0\ (X\le\ell_i,\ Y\ge0),\qquad \partial_Y\Phi_i(X,Y)=0\ (X\in\mathbb R,\ Y\ge\ell_{i+1}),$$
--   and, for every $b_i>8$, the iterations (9) with $f_j=0$ satisfy the transfer conditions (8), and
--   $$\frac{D_{i+1}}{D_i}\ge\frac{b_i-8}{c_\beta(a_\beta+s_i+8)}\,\eta_i\Bigl(1-\frac{s_i}\kappa\Bigr),\qquad \frac{\ell_{i+1}}{D_{i+1}}\le4\,\frac{s_i+2}{b_i-8}.$$
--
--   This is the basic transfer guarantee of the bending component; its factor $(b_i-8)/(c_\beta(a_\beta+s_i+8))$ defines the checkpoint score (18).
--
--   Differences from the source:
--   - encoding: standing setup of §3 (p.13): input threshold ℓ_i ≥ 0, incoming excess D_i > 0, gap stepsizes h_j ≥ 0 → explicit hypotheses hℓ, hD, hh; reason: standing assumptions of the section, stated once on p.13
--   - encoding: D_{i+1} determined by Y_{m_gap+1} = ℓ_{i+1} + D_{i+1} → outExcess κ Φ hs b ℓ D ℓ' f, and (8) is IsTransfer; reason: D_{i+1} is not a free quantity; the predicate is (8) verbatim
--   - encoding: f_j = 0 → the zero sequence fun _ => 0; reason: same
--   - encoding: functions on ℝ², ∂_Y, 1-smooth, Π_K → EuclideanSpace ℝ (Fin 2), coordinate 1 of gradient, KatyushaNs.IsConvexLSmooth 1, OrabonaOL.OGD.IsEuclideanProj; reason: Lean representation; same objects
--   - encoding: gap stepsizes h_1, …, h_{m_gap}, their sum s_i, χ_i, η_i, the standing h_j < κ → hs : List ℝ, s_i = hs.sum, chiGap, etaGap; no separate hypothesis h_j < κ; reason: same data; h_j ≥ 0 and s_i/κ ≤ 1/16 imply h_j ≤ κ/16 < κ
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma 3.1, p.15; setting §3, pp.13–14

import Mathlib
import Definitions.Def_SilverRateSC_aBeta
import Definitions.Def_SilverRateSC_etaGap
import Definitions.Def_SilverRateSC_IsTransfer
import Definitions.Def_SilverRateSC_IsLocalComponent

namespace SilverRateSC

/-- **Lemma 3.1 (Bending).** Let `κ ≥ 4`, `0 < β ≤ 1/4`, `s_i/κ ≤ 1/16`, and `η_i > 0`. There
exist a nonnegative convex `1`-smooth local hard function `Φ_i` and a threshold `ℓ_{i+1} ≥ 0`,
independent of the checkpoint stepsize `b_i`, such that `∂_YΦ_i ≤ 0` everywhere and
`Φ_i(X, Y) = 0` (`X ≤ ℓ_i`, `Y ≥ 0`), `∂_YΦ_i(X, Y) = 0` (`X ∈ ℝ`, `Y ≥ ℓ_{i+1}`). For every
`b_i > 8`, the iterations (9) with `f_j = 0` satisfy (8), and
`D_{i+1}/D_i ≥ (b_i − 8)/(c_β(a_β + s_i + 8)) η_i(1 − s_i/κ)`,
`ℓ_{i+1}/D_{i+1} ≤ 4(s_i + 2)/(b_i − 8)` (12).

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma 3.1, p. 15 (setting of §3, pp. 13–14).

**Formalization Note** The setting of §3 is explicit: input threshold `ℓ_i ≥ 0`, incoming excess
`D_i > 0`, nonnegative gap stepsizes `hs` (the standing `h_j < κ` follows from
`s_i/κ ≤ 1/16`), `η_i = etaGap κ hs ℓ_i D_i`. `∃ Φ ℓ'` precedes `∀ b > 8`, so the component does
not depend on `b_i`. `D_{i+1}` is `outExcess …` (`Y_{m_gap+1} − ℓ_{i+1}`), with `f_j = 0`. -/
theorem lemma_3_1 (κ β ℓ D : ℝ) (hs : List ℝ) (hκ : 4 ≤ κ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 4)
    (hℓ : 0 ≤ ℓ) (hD : 0 < D) (hh : ∀ h ∈ hs, 0 ≤ h) (hsκ : hs.sum / κ ≤ 1 / 16)
    (hη : 0 < etaGap κ hs ℓ D) :
    ∃ (Φ : EuclideanSpace ℝ (Fin 2) → ℝ) (ℓ' : ℝ), 0 ≤ ℓ' ∧ IsLocalComponent Φ ℓ ∧
      IsFlatAbove Φ ℓ' ∧
      ∀ b : ℝ, 8 < b →
        IsTransfer κ Φ hs b ℓ D ℓ' (fun _ => 0) ∧
        (b - 8) / (cBeta β * (aBeta β + hs.sum + 8)) * etaGap κ hs ℓ D * (1 - hs.sum / κ) ≤
          outExcess κ Φ hs b ℓ D ℓ' (fun _ => 0) / D ∧
        ℓ' / outExcess κ Φ hs b ℓ D ℓ' (fun _ => 0) ≤ 4 * (hs.sum + 2) / (b - 8) := by sorry

end SilverRateSC
