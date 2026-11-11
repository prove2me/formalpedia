-- Prove2me | Theorems.Thm_SwapDisk_Main_proposition_B_3
-- name    : SwapDisk.Main.proposition_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:18:28.09601+00:00
-- url     : https://prove2.me/theorems/85e77204-4faa-46c4-9205-d1a29917cc41
-- title:
--   Proposition B.3 — feasible weighted responses: $\min_q F_\kappa(q)=\min_q\max_g L_\kappa(q,g)\le 0$ and a Borel dyadic $\epsilon$-response selector exists
-- statement:
--   Let $T\ge2$, $\gamma\in\Gamma_T$, nets satisfying (B.3). For every $\kappa\in\Delta(C)$,
--   $$\min_{q\in\Delta(J)}F_\kappa(q)=\min_{q\in\Delta(J)}\max_{g\in B^2_2}L_\kappa(q,g)\le0 .$$
--   For every fixed $\epsilon>0$ there is a Borel map $q_\epsilon:\Delta(C)\to\Delta(J)$ with dyadic rational coordinates such that
--   $$L_\kappa(q_\epsilon(\kappa),g)\le\epsilon\qquad\text{for every }\kappa\in\Delta(C),\ g\in B^2_2 .$$
--
--   The selector is SHARP's response map (with $\epsilon=1/T$).
--
--   Differences from the source:
--   - encoding: γ ∈ Γ_T = {2^{−k} : 0 ≤ k ≤ ⌊log₂ T⌋} → γ = `gam ell` = 2^{−ℓ} with `ell ≤ Nat.log 2 T`; reason: the same set of resolutions, indexed by ℓ_γ = log₂(1/γ)
--   - encoding: angular r_s-nets X_s ⊆ S¹ with |X_s| ≤ 16/r_s (Eq. (B.3)), angular distance = shorter arc → `NetsOK ell X`: `X k` a `Finset` of unit vectors, every unit `u` within `arccos ⟨u, x⟩ ≤ r_k` of some `x ∈ X k`, and `card (X k) ≤ 16 / r_k`; reason: arccos⟨u, x⟩ is the length of the shorter arc between unit vectors; same nets
--   - encoding: tags J = {0} ∪ {(s, x)}, constraints h_c of Eqs. (B.6)–(B.7) → `Tag ell X = Option (Σ k, X k)` (`none` = 0); `hval c g = hconst c + ⟨hvec c, g⟩`; centre constraints indexed by `(i, σ) ∈ Fin 2 × Bool` (0-based coordinate, `true` = +1); reason: the same tags and the same affine maps
--   - encoding: min_q F_κ(q) = min_q max_g L_κ(q, g) ≤ 0 → for every q ∈ Δ(J), F_κ(q) is the greatest value of g ↦ L_κ(q, g) on B²₂ (`IsGreatest`), and some q₀ ∈ Δ(J) minimizes F_κ with F_κ(q₀) ≤ 0; reason: the two objectives agree at every q, so both minima exist and coincide; equivalent
--   - encoding: a Borel map q_ε : Δ(C) → Δ(J) → a Borel map `(C → ℝ) → (J → ℝ)` whose values on Δ(C) lie in Δ(J); reason: Δ(C) is a closed subset; a Borel map on it extends Borel-measurably (constant off Δ(C)) and the extension restricts back
--   - encoding: dyadic rational coordinates → each coordinate equals m / 2^n with m, n ∈ ℕ; reason: nonnegative dyadic rationals
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 23, Proposition B.3

import Mathlib
import Definitions.Def_SwapDisk_Main_Sharp

namespace SwapDisk.Main

/-- Proposition B.3 (Feasible weighted responses), p. 23: for every `κ ∈ Δ(C)`,
`min_{q ∈ Δ(J)} F_κ(q) = min_{q ∈ Δ(J)} max_{g ∈ B²₂} L_κ(q, g) ≤ 0` (each `F_κ(q)` is the
attained maximum over `g`, and the minimum over `q` is attained and nonpositive); and for every
`ε > 0` there is a Borel map `q_ε : Δ(C) → Δ(J)` with dyadic rational coordinates and
`L_κ(q_ε(κ), g) ≤ ε` for all `κ ∈ Δ(C)`, `g ∈ B²₂`. -/
theorem proposition_B_3 (T ell : ℕ) (hT : 2 ≤ T) (hell : ell ≤ Nat.log 2 T)
    (X : Fin (ell + 1) → Finset E2) (hX : NetsOK ell X) :
    (∀ κ ∈ simplex (Con ell X),
      (∀ q ∈ simplex (Tag ell X),
        IsGreatest (Set.range fun g : Disk => Lkappa κ q (g : E2)) (Fkappa κ q)) ∧
      ∃ q₀ ∈ simplex (Tag ell X),
        (∀ q ∈ simplex (Tag ell X), Fkappa κ q₀ ≤ Fkappa κ q) ∧ Fkappa κ q₀ ≤ 0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ sel : (Con ell X → ℝ) → (Tag ell X → ℝ), Measurable sel ∧
      ∀ κ ∈ simplex (Con ell X), sel κ ∈ simplex (Tag ell X) ∧
        (∀ j, ∃ m n : ℕ, sel κ j = (m : ℝ) / 2 ^ n) ∧
        ∀ g : Disk, Lkappa κ (sel κ) (g : E2) ≤ ε := by sorry

end SwapDisk.Main
