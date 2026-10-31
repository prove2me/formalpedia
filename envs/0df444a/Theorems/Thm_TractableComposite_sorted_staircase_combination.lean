-- Prove2me | Theorems.Thm_TractableComposite_sorted_staircase_combination
-- name    : TractableComposite.sorted_staircase_combination
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:39.839314+00:00
-- url     : https://prove2.me/theorems/dd25841a-de89-4afd-bcd7-65de4fc133f6
-- title:
--   §3.1, display after (9) — $\bar s$ is a convex combination of the sorted staircase's vertices
-- statement:
--   Let $\bar s\in Q$ and $\bar z=Z(\bar s)$. Let $\pi$ be a movement vector that sorts $\bar z$: writing $\Theta(k)=(\pi(k),\Pi(\pi,k)_{\pi(k)})$ for the coordinate moved at step $k$, the values $z_{\Theta(1)}\ge z_{\Theta(2)}\ge\dots\ge z_{\Theta(dn)}$. Then
--
--   $$\bar s=(1-z_{\Theta(1)})\mathcal V(\pi,0)+\sum_{k=1}^{dn-1}(z_{\Theta(k)}-z_{\Theta(k+1)})\mathcal V(\pi,k)+z_{\Theta(dn)}\mathcal V(\pi,dn),$$
--
--   and in particular $\bar s\in\Upsilon_\pi$. This is why sorting $\bar z$ finds the staircase simplex containing $\bar s$ in Algorithm 1.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - encoding: sort z̄ (z̄_i0 placed first; z̄_ij ahead of z̄_ij′ for j < j′ on ties), Θ(k) the (d+k)-th largest, π = Θ₁ → π a movement vector with k ↦ z̄_{Θ(k)} non-increasing, Θ(k) = (π(k), Π(π,k)_{π(k)}); reason: a movement vector determines Θ₂ by counting (p.8), which is the within-row order; every sorting of z̄ is such a π
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), §3.1, display after (9), p.12

import Mathlib
import Definitions.Def_TractableComposite_Q
import Definitions.Def_TractableComposite_vtx
import Definitions.Def_TractableComposite_IsMovement
import Definitions.Def_TractableComposite_gridPt
import Definitions.Def_TractableComposite_stairVtx
import Definitions.Def_TractableComposite_stairSimplex
import Definitions.Def_TractableComposite_Zmap

namespace TractableComposite

/-- **§3.1, display after (9), p.12: `s̄` is a convex combination of the staircase vertices of the
sorted order.** He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.12.

Let `s̄ ∈ Q` and `z̄ = Z(s̄)` (11). Sort the coordinates `z̄ᵢⱼ`, `j ≥ 1`, in non-increasing order (the `z̄ᵢ₀ = 1`
placed first), with `z̄ᵢⱼ` ahead of `z̄ᵢⱼ'` for `j < j'`; if the `(d+k)`-th largest coordinate is `z̄ᵢⱼ`, put
`Θ(k) = (i,j)` and `π = (Θ₁(1), …, Θ₁(dn))`. Then
`s̄ = (1 − z_{Θ(1)}) 𝒱(π,0) + ∑_{k=1}^{dn−1} (z_{Θ(k)} − z_{Θ(k+1)}) 𝒱(π,k) + z_{Θ(dn)} 𝒱(π,dn)`, so `s̄ ∈ Υ_π`.

**Formalization Note.** The sorted order is given by its movement vector `π` (0-based: `π t` is the
`(t+1)`-th move). For `π`, `Θ(k) = (π(k), Π(π,k)_{π(k)})` (the `k`-th move is the `Θ₂(k)`-th step in its
direction, p.8), so "sorted" is the hypothesis `hsort`: `k ↦ z̄_{Θ(k)}` is non-increasing; this covers
every sorting of `z̄` (ties in any order across rows). `zΘ k` is `z̄_{Θ(k)}` for `1 ≤ k ≤ dn`. -/
theorem sorted_staircase_combination {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (a : Fin d → Fin (n + 1) → ℝ) (ha : ∀ i, StrictMono (a i)) (s : Fin d → Fin (n + 1) → ℝ) (hs : s ∈ Q a)
    (π : Fin (d * n) → Fin d) (hπ : IsMovement π)
    (hsort : ∀ k k' : Fin (d * n), k ≤ k' →
      Zmap a s (π k') (gridPt π (k'.val + 1) (π k')) ≤ Zmap a s (π k) (gridPt π (k.val + 1) (π k))) :
    let zΘ : ℕ → ℝ := fun k =>
      if h : 1 ≤ k ∧ k ≤ d * n then
        Zmap a s (π ⟨k - 1, by omega⟩) (gridPt π k (π ⟨k - 1, by omega⟩))
      else 0
    s = (1 - zΘ 1) • stairVtx (vtx a) π 0 +
        ∑ k ∈ Finset.Ico 1 (d * n), (zΘ k - zΘ (k + 1)) • stairVtx (vtx a) π k +
        zΘ (d * n) • stairVtx (vtx a) π (d * n) ∧
      s ∈ stairSimplex (vtx a) π := by sorry

end TractableComposite
