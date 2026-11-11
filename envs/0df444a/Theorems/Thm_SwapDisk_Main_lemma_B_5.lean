-- Prove2me | Theorems.Thm_SwapDisk_Main_lemma_B_5
-- name    : SwapDisk.Main.lemma_B_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:18:22.758129+00:00
-- url     : https://prove2.me/theorems/cb77d286-ca22-41f0-b926-a0034525b692
-- title:
--   Lemma B.5 — truncated-rate curvature control: certificate sums at every grid rate give $\sqrt{a^2+b^2}-a\le 592(sr^2m+\lambda/s)$
-- statement:
--   Fix a level $k$, let $s=s_k$, $r=r_k$ and $\lambda\ge1$, and use the grid $H_k=\{s2^{-\ell'}/16:0\le\ell'\le k\}$. Suppose $m\ge0$, $a,b\in\mathbb R$ and each of the three quantities
--   $$S_{\mathrm{rad}}=sm/2-a,\qquad S_\pm=\pm b-2srm$$
--   is at most $4\eta m+\lambda/\eta$ for every $\eta\in H_k$. Then
--   $$\sqrt{a^2+b^2}-a\le592\Big(sr^2m+\frac\lambda s\Big).$$
--
--   This converts realized certificate sums at a boundary tag into a bound on its support defect.
--
--   Differences from the source:
--   - generalization: γ ∈ Γ_T for a horizon T ≥ 2 → γ = 2^{−ℓ} for every ℓ ∈ ℕ, level k ≤ ℓ, no horizon; reason: the lemma does not involve T; Γ_T is a subset of these resolutions
--   - encoding: each of the three quantities in (B.16) is at most 4ηm + λ/η for every η ∈ H_k → for every ℓ' ≤ k, with η = s_k 2^{−ℓ'}/16, the three inequalities written out; reason: the same grid and the same quantities
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 24, Lemma B.5

import Mathlib
import Definitions.Def_SwapDisk_Main_Sharp

namespace SwapDisk.Main

/-- Lemma B.5 (Truncated-rate curvature control), p. 24: fix a level `k`, `s = s_k`, `r = r_k`,
`λ ≥ 1`, the grid `H_k = {s 2^{−ℓ'}/16 : 0 ≤ ℓ' ≤ k}`; if `m ≥ 0`, `a, b ∈ ℝ` and each of
`S_rad = sm/2 − a`, `S_± = ±b − 2srm` (Eq. (B.16)) is at most `4ηm + λ/η` for every `η ∈ H_k`,
then `√(a² + b²) − a ≤ 592 (s r² m + λ/s)`. -/
theorem lemma_B_5 (ell k : ℕ) (hk : k ≤ ell) (lam m a b : ℝ) (hlam : 1 ≤ lam) (hm : 0 ≤ m)
    (hS : ∀ l : ℕ, l ≤ k →
      scale ell k * m / 2 - a ≤
          4 * (scale ell k * (2 : ℝ) ^ (-(l : ℤ)) / 16) * m +
            lam / (scale ell k * (2 : ℝ) ^ (-(l : ℤ)) / 16) ∧
      b - 2 * scale ell k * radius k * m ≤
          4 * (scale ell k * (2 : ℝ) ^ (-(l : ℤ)) / 16) * m +
            lam / (scale ell k * (2 : ℝ) ^ (-(l : ℤ)) / 16) ∧
      -b - 2 * scale ell k * radius k * m ≤
          4 * (scale ell k * (2 : ℝ) ^ (-(l : ℤ)) / 16) * m +
            lam / (scale ell k * (2 : ℝ) ^ (-(l : ℤ)) / 16)) :
    Real.sqrt (a ^ 2 + b ^ 2) - a ≤
      592 * (scale ell k * radius k ^ 2 * m + lam / scale ell k) := by sorry

end SwapDisk.Main
