-- Prove2me | Theorems.Thm_SwapDisk_Main_lemma_B_6
-- name    : SwapDisk.Main.lemma_B_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:17:48.277492+00:00
-- url     : https://prove2.me/theorems/e6871ed2-3000-46a2-844c-9cfc81b1e086
-- title:
--   Lemma B.6 — deterministic product-to-certificate bounds: $S_{c,T}\le\eta\sum_t f_{c,t}^2+\log(B/\pi_{c,\eta})/\eta\le 4\eta m_{j(c)}+\log(B/\pi_{c,\eta})/\eta$
-- statement:
--   Consider a finite constraint–rate family with positive prior weights $\pi_{c,\eta}$ summing to one, rates $0<\eta\le1/4$, scalar updates $f_{c,t}=1\{J_t=j(c)\}h_c(g_t)$ with $|h_c|\le2$ on $B^2_2$, and products $W_{c,\eta,0}=\pi_{c,\eta}$, $W_{c,\eta,t}=W_{c,\eta,t-1}(1+\eta f_{c,t})$. If $\Psi_T=\sum_{c,\eta}W_{c,\eta,T}\le B$, then for every pair
--   $$S_{c,T}\le\eta\sum_tf_{c,t}^2+\frac{\log(B/\pi_{c,\eta})}\eta\le4\eta m_{j(c)}+\frac{\log(B/\pi_{c,\eta})}\eta ,$$
--   with $S_{c,T}=\sum_tf_{c,t}$ and $m_j=|\{t:J_t=j\}|$.
--
--   This is the deterministic half of the potential argument: a bounded potential certifies every constraint at every rate.
--
--   Differences from the source:
--   - generalization: a finite constraint–rate family of pairs (c, η) → pairs indexed by a finite type P with maps con : P → C, η, π (C and the tag type J arbitrary; two indices may carry the same (c, η)); reason: a finite set of distinct pairs is the special case of an injective index
--   - encoding: W_{c,η,T} defined by the recursion from W_{c,η,0} = π_{c,η} → the closed-form product π_p ∏_t (1 + η_p f_{con p, t}); reason: the recursion unrolled; same values
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 26, Lemma B.6

import Mathlib
import Definitions.Def_SwapDisk_Main_Regret

namespace SwapDisk.Main

/-- Lemma B.6 (Deterministic product-to-certificate bounds), p. 26: for a finite constraint–rate
family (pairs `p` with constraint `con p`, rate `0 < η_p ≤ 1/4`, prior `π_p > 0`, `∑ π_p = 1`),
scalar updates `f_{c,t} = 1{J_t = j(c)} h_c(g_t)` with `|h_c| ≤ 2`, products
`W_{p,T} = π_p ∏_t (1 + η_p f_{con p,t})`, if `Ψ_T = ∑_p W_{p,T} ≤ B` then
`S_{c,T} ≤ η ∑_t f_{c,t}² + log(B/π)/η ≤ 4η m_{j(c)} + log(B/π)/η`. -/
theorem lemma_B_6 {J C P : Type} [Fintype P] [DecidableEq J] (T : ℕ) (con : P → C)
    (η π : P → ℝ) (jc : C → J) (hc : C → E2 → ℝ)
    (hπ : ∀ p, 0 < π p) (hπsum : ∑ p, π p = 1) (hη : ∀ p, 0 < η p ∧ η p ≤ 1 / 4)
    (hh : ∀ (c : C) (g : Disk), |hc c (g : E2)| ≤ 2)
    (tag : Fin T → J) (g : Fin T → Disk) (B : ℝ)
    (hB : ∑ p, π p * ∏ t, (1 + η p * (if tag t = jc (con p) then hc (con p) (g t : E2) else 0))
      ≤ B) (p : P) :
    ∑ t, (if tag t = jc (con p) then hc (con p) (g t : E2) else 0) ≤
        η p * ∑ t, (if tag t = jc (con p) then hc (con p) (g t : E2) else 0) ^ 2 +
          Real.log (B / π p) / η p ∧
    η p * ∑ t, (if tag t = jc (con p) then hc (con p) (g t : E2) else 0) ^ 2 +
          Real.log (B / π p) / η p ≤
        4 * η p * tagCount tag (jc (con p)) + Real.log (B / π p) / η p := by sorry

end SwapDisk.Main
