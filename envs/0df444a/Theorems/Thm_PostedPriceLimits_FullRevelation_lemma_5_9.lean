-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_lemma_5_9
-- name    : PostedPriceLimits.FullRevelation.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:23.326434+00:00
-- url     : https://prove2.me/theorems/0a7864e7-3e07-4346-9b8b-d300bb8711eb
-- title:
--   Lemma 5.9 — Pythagorean identity for the cell-average projection
-- statement:
--   In the setting of §5, fix a realisation of the randomness, a block $t$, a name set $L$ and prices $p\in[0,\infty]^{Z_t}$, and let $B_{t,p}(k,x)=(1-p_x/(2\mathrm{val}(k)))_+$. For every $\mathcal P_{t,L}$-measurable $A:[\kappa]\times Z_t\to[0,1]$,
--   $$\mathrm{Avg}[(A-B_{t,p})^2]=\mathrm{Avg}[(A-\Pi_{t,L}B_{t,p})^2]+\mathrm{Avg}[(\Pi_{t,L}B_{t,p}-B_{t,p})^2],$$
--   where $\mathrm{Avg}$ is the uniform average over $[\kappa]\times Z_t$ and $(\Pi_{t,L}B)(k,x)$ is the average of $B(k,\cdot)$ over the part of $\mathcal P_{t,L}$ containing $x$.
--
--   It is used in the proof of Proposition 5.5-(2) to compare the selected grid function with the projection of $B_{t,p}$.
--
--   Differences from the source:
--   - generalization: B_{t,p} for the prices posted by the mechanism, for sufficiently large n (§5 standing assumption) → every price vector p, every n and every latent point without IsRealisation; reason: the identity uses only averaging on the partition induced by ψ′; this is a partition even outside the support of the sampling law, and every source case is included
--   - encoding: A : [κ] × Z_t → [0,1] P_{t,L}-measurable → A : ℕ → Z_t → ℝ with values in [0,1] and P_{t,L}-measurable sections on [κ]; reason: only values on [κ] × Z_t enter
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma 5.9, p.21 (PDF 22); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction
import Definitions.Def_PostedPriceLimits_FullRevelation_Analysis
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation

/-- Lemma 5.9. For every `𝒫_{t,L}`-measurable `A : [κ] × Z_t → [0,1]`,
`Avg[(A − B_{t,p})²] = Avg[(A − Π_{t,L} B_{t,p})²] + Avg[(Π_{t,L} B_{t,p} − B_{t,p})²]`. -/
theorem lemma_5_9 (n : ℕ) (ω : Latent n) (t : Fin n) (L : Finset (Fin (poolSize n)))
    (p : Fin (blockSize n) → ℝ≥0∞) (A : ℕ → Fin (blockSize n) → ℝ)
    (hA : ∀ k ∈ rankRange (kappa n), ∀ x, A k x ∈ Set.Icc (0 : ℝ) 1)
    (hAmeas : ∀ k ∈ rankRange (kappa n), IsCellMeasurable ω t L (A k)) :
    avgRK n (fun k x => (A k x - affordFn n p k x) ^ 2) =
      avgRK n (fun k x => (A k x - proj ω t L (affordFn n p) k x) ^ 2) +
        avgRK n (fun k x => (proj ω t L (affordFn n p) k x - affordFn n p k x) ^ 2) := by sorry

end PostedPriceLimits.FullRevelation
