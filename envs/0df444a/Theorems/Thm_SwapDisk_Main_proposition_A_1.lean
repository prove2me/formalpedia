-- Prove2me | Theorems.Thm_SwapDisk_Main_proposition_A_1
-- name    : SwapDisk.Main.proposition_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:17:25.291164+00:00
-- url     : https://prove2.me/theorems/16f1cc06-e4d5-4b68-8b84-107aec64d46f
-- title:
--   Proposition A.1 — regrouping by physical actions: $R_T=\sum_{x\in X_T}\psi_x(G_x)$, attained by a Borel deviation, Borel in the transcript, $0\le R_T\le 2T$
-- statement:
--   For a realized transcript $(x_t,g_t)_{t=1}^T$ in $B^2_2\times B^2_2$ let $X_T=\{x_1,\dots,x_T\}$ and $G_x=\sum_{t:x_t=x}g_t$. Then
--   $$R_T=\sum_{x\in X_T}\psi_x(G_x).$$
--   The supremum defining $R_T$ is attained by a Borel deviation, $R_T$ is a Borel function of the finite transcript, $0\le R_T\le2T$, and the supremum over all (possibly nonmeasurable) maps $B^2_2\to B^2_2$ has the same value.
--
--   This turns the hindsight benchmark into a finite formula and makes $\mathbb E[R_T]$ an ordinary expectation.
--
--   Differences from the source:
--   - generalization: a horizon T ≥ 2 (standing assumption) → every T ∈ ℕ; reason: T ≥ 2 is a special case
--   - encoding: Borel function of the finite transcript in (B²₂ × B²₂)^T → `Measurable` on `(Fin T → Disk) × (Fin T → Disk)` with the product σ-field; reason: product of Borel σ-fields of Polish spaces is the Borel σ-field; same transcripts
--   - encoding: the supremum over arbitrary, possibly nonmeasurable deviations → the real `⨆` over all maps `Disk → Disk`; reason: the family is bounded above by 2T, so the real `⨆` is the supremum
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 14, Proposition A.1

import Mathlib
import Definitions.Def_SwapDisk_Main_Regret

open scoped Classical

namespace SwapDisk.Main

/-- Proposition A.1 (Regrouping by physical actions), p. 14: `R_T = ∑_{x ∈ X_T} ψ_x(G_x)` with
`X_T = {x_1, …, x_T}` and `G_x = ∑_{t : x_t = x} g_t`; the supremum is attained by a Borel
deviation; `R_T` is a Borel function of the transcript; `0 ≤ R_T ≤ 2T`; the supremum over all
(possibly nonmeasurable) maps has the same value. -/
theorem proposition_A_1 (T : ℕ) (x g : Fin T → Disk) :
    swapRegret x g = ∑ y ∈ Finset.univ.image x,
        psi (y : E2) (∑ t ∈ Finset.univ.filter (fun t => x t = y), (g t : E2)) ∧
    (∃ φ : Disk → Disk, Measurable φ ∧ gain x g Finset.univ φ = swapRegret x g) ∧
    Measurable (fun p : (Fin T → Disk) × (Fin T → Disk) => swapRegret p.1 p.2) ∧
    0 ≤ swapRegret x g ∧ swapRegret x g ≤ 2 * T ∧
    (⨆ φ : Disk → Disk, gain x g Finset.univ φ) = swapRegret x g := by sorry

end SwapDisk.Main
