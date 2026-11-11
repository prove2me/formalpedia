-- Prove2me | Theorems.Thm_SwapDisk_Main_lemma_B_1
-- name    : SwapDisk.Main.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:18:37.305562+00:00
-- url     : https://prove2.me/theorems/62c35e65-0038-48ad-af82-4fca18c6bcab
-- title:
--   Lemma B.1 — dictionary and summation bounds: $M\le 1+C_{\mathrm{cov}}\gamma^{-1/2}$, $\sum_s|X_s|/s\le C_{\mathrm{cov}}/\gamma$, $C_{\mathrm{cov}}=256/(1-2^{-1/2})$
-- statement:
--   Let $T\ge2$, $\gamma\in\Gamma_T$, and let the nets $X_s$ satisfy (B.3). With $C_{\mathrm{cov}}=256/(1-2^{-1/2})$ the tagged dictionary $J$ has $M=|J|$ with
--   $$M\le1+C_{\mathrm{cov}}\gamma^{-1/2},\qquad\sum_{s\in S_\gamma}\frac{|X_s|}{s}\le\frac{C_{\mathrm{cov}}}\gamma .$$
--
--   The first bound is the dictionary budget; the second controls the statistical charges summed over scales.
--
--   Differences from the source:
--   - encoding: γ ∈ Γ_T = {2^{−k} : 0 ≤ k ≤ ⌊log₂ T⌋} → γ = `gam ell` = 2^{−ℓ} with `ell ≤ Nat.log 2 T`; reason: the same set of resolutions, indexed by ℓ_γ = log₂(1/γ)
--   - encoding: angular r_s-nets X_s ⊆ S¹ with |X_s| ≤ 16/r_s (Eq. (B.3)), angular distance = shorter arc → `NetsOK ell X`: `X k` a `Finset` of unit vectors, every unit `u` within `arccos ⟨u, x⟩ ≤ r_k` of some `x ∈ X k`, and `card (X k) ≤ 16 / r_k`; reason: arccos⟨u, x⟩ is the length of the shorter arc between unit vectors; same nets
--   - encoding: M = |J| → `Fintype.card (Tag ell X)`; reason: J is the type of tags
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 22, Lemma B.1

import Mathlib
import Definitions.Def_SwapDisk_Main_Sharp

namespace SwapDisk.Main

/-- Lemma B.1 (Dictionary and summation bounds), p. 22: with `C_cov = 256/(1 − 2^{−1/2})`,
`M ≤ 1 + C_cov γ^{−1/2}` and `∑_{s ∈ S_γ} |X_s|/s ≤ C_cov/γ`, for `γ = 2^{−ℓ} ∈ Γ_T` and any nets
satisfying (B.3). -/
theorem lemma_B_1 (T ell : ℕ) (hT : 2 ≤ T) (hell : ell ≤ Nat.log 2 T)
    (X : Fin (ell + 1) → Finset E2) (hX : NetsOK ell X) :
    (Fintype.card (Tag ell X) : ℝ) ≤
        1 + 256 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) * gam ell ^ (-(1 / 2 : ℝ)) ∧
    ∑ k : Fin (ell + 1), ((X k).card : ℝ) / scale ell k ≤
        256 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) / gam ell := by sorry

end SwapDisk.Main
