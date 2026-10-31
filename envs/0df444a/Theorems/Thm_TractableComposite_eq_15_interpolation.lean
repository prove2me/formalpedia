-- Prove2me | Theorems.Thm_TractableComposite_eq_15_interpolation
-- name    : TractableComposite.eq_15_interpolation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:21.442076+00:00
-- url     : https://prove2.me/theorems/11dee90e-6857-4bbc-a065-73259fad991b
-- title:
--   (15) — the affine function interpolating $\bar\phi$ on a staircase simplex
-- statement:
--   Let $\pi$ be a movement vector and let $\alpha^\pi,b^\pi$ be given by (15). Then
--
--   1. $\alpha^\pi_{i0}=0$ for every $i$;
--   2. $\langle\alpha^\pi,\mathcal V(\pi,k)\rangle+b^\pi=\bar\phi(\mathcal V(\pi,k))$ for $k=0,\dots,dn$;
--   3. $(\alpha^\pi,b^\pi)$ is the only pair $(\alpha,b)$ with $\alpha_{i0}=0$ for all $i$ that satisfies 2.
--
--   So $\langle\alpha^\pi,s\rangle+b^\pi$ is the unique affine function of this form interpolating $\bar\phi$ at the vertices of $\Upsilon_\pi$; Algorithm 1 returns it.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - encoding: m(i,j) = k if π(k) = i and j = ∑_{k′≤k} 𝟙(π(k′) = π(k)) → the least k with Π(π,k)ᵢ ≥ j (sInf over ℕ); reason: the k-th move is the j-th step in direction i exactly when the count in direction i first reaches j at k; same value for 1 ≤ j ≤ n and a movement vector
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (15), p.11

import Mathlib
import Definitions.Def_TractableComposite_ip
import Definitions.Def_TractableComposite_phiBar
import Definitions.Def_TractableComposite_vtx
import Definitions.Def_TractableComposite_IsMovement
import Definitions.Def_TractableComposite_stairVtx
import Definitions.Def_TractableComposite_alphaPi
import Definitions.Def_TractableComposite_bPi

namespace TractableComposite

/-- **(15), p.11: the affine function interpolating φ̄ on a staircase simplex.** He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.11, (15).

For a movement vector `π`, `⟨α^π, s⟩ + b^π` with `α^π`, `b^π` given by (15) is the unique affine function
with `α^π_i0 = 0` for all `i` and `φ̄(s) = ⟨α^π, s⟩ + b^π` at the vertices `𝒱(π,0), …, 𝒱(π,dn)` of `Υ_π`.

**Formalization Note.** Uniqueness ("the unique affine function", p.11) is stated as a clause: any
`(α, b)` with `αᵢ₀ = 0` that interpolates `φ̄` at the `dn + 1` vertices equals `(α^π, b^π)`. `φ` is
continuous (standing assumption of §2, p.3). -/
theorem eq_15_interpolation {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (a : Fin d → Fin (n + 1) → ℝ) (ha : ∀ i, StrictMono (a i)) (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ)
    (π : Fin (d * n) → Fin d) (hπ : IsMovement π) :
    (∀ i, alphaPi a φ π i 0 = 0) ∧
    (∀ k : Fin (d * n + 1),
      ip (alphaPi a φ π) (stairVtx (vtx a) π k) + bPi a φ π = phiBar φ (stairVtx (vtx a) π k)) ∧
    ∀ (α : Fin d → Fin (n + 1) → ℝ) (b : ℝ), (∀ i, α i 0 = 0) →
      (∀ k : Fin (d * n + 1), ip α (stairVtx (vtx a) π k) + b = phiBar φ (stairVtx (vtx a) π k)) →
      α = alphaPi a φ π ∧ b = bPi a φ π := by sorry

end TractableComposite
