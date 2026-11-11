-- Prove2me | Theorems.Thm_SwapDisk_Main_lemma_B_2
-- name    : SwapDisk.Main.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:18:41.235449+00:00
-- url     : https://prove2.me/theorems/d6d5927c-1dc0-4275-b544-c3923c253a1b
-- title:
--   Lemma B.2 — a simultaneous pure response: every $\mu\in B^2_2$ has a tag all of whose constraints are nonpositive at $\mu$
-- statement:
--   Let $T\ge2$, $\gamma\in\Gamma_T$, and let the nets satisfy (B.3). For every $\mu\in B^2_2$ there is a tag $j\in J$ such that
--   $$h_c(\mu)\le0\quad\text{for every constraint }c\text{ carried by }j .$$
--
--   This geometric feasibility statement is what makes the weighted response problem feasible (Proposition B.3).
--
--   Differences from the source:
--   - encoding: γ ∈ Γ_T = {2^{−k} : 0 ≤ k ≤ ⌊log₂ T⌋} → γ = `gam ell` = 2^{−ℓ} with `ell ≤ Nat.log 2 T`; reason: the same set of resolutions, indexed by ℓ_γ = log₂(1/γ)
--   - encoding: angular r_s-nets X_s ⊆ S¹ with |X_s| ≤ 16/r_s (Eq. (B.3)), angular distance = shorter arc → `NetsOK ell X`: `X k` a `Finset` of unit vectors, every unit `u` within `arccos ⟨u, x⟩ ≤ r_k` of some `x ∈ X k`, and `card (X k) ≤ 16 / r_k`; reason: arccos⟨u, x⟩ is the length of the shorter arc between unit vectors; same nets
--   - encoding: tags J = {0} ∪ {(s, x)}, constraints h_c of Eqs. (B.6)–(B.7) → `Tag ell X = Option (Σ k, X k)` (`none` = 0); `hval c g = hconst c + ⟨hvec c, g⟩`; centre constraints indexed by `(i, σ) ∈ Fin 2 × Bool` (0-based coordinate, `true` = +1); reason: the same tags and the same affine maps
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 22, Lemma B.2

import Mathlib
import Definitions.Def_SwapDisk_Main_Sharp

namespace SwapDisk.Main

/-- Lemma B.2 (A simultaneous pure response), p. 22: for every `µ ∈ B²₂` some tag `j` has
`h_c(µ) ≤ 0` for every constraint `c` carried by `j`. -/
theorem lemma_B_2 (T ell : ℕ) (hT : 2 ≤ T) (hell : ell ≤ Nat.log 2 T)
    (X : Fin (ell + 1) → Finset E2) (hX : NetsOK ell X) :
    ∀ μ : Disk, ∃ j : Tag ell X, ∀ c : Con ell X, conTag c = j → hval c (μ : E2) ≤ 0 := by sorry

end SwapDisk.Main
