-- Prove2me | Theorems.Thm_WernerExt_TwoSided_werner_extendibility
-- name    : WernerExt.TwoSided.werner_extendibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:36.199983+00:00
-- url     : https://prove2.me/theorems/f5d0f33b-f144-4a50-8168-2d47053695a1
-- title:
--   Eqs. (12)–(13), pp. 3–4 (corrected: the minimum is over all pairs; Eqs. (13), (15), (16) are false) — ρ_W(α) is (n_A, n_B)-extendible iff α ≥ min E_W
-- statement:
--   Let $d\ge2$ be the local dimension, $n_A,n_B\ge1$ the extension sizes, and $\alpha\in[-1,1]$. The Werner state
--   $$\rho^W(\alpha)=\frac{d}{d^2-1}\left[(d-\alpha)\frac{\mathbb 1}{d^2}+\left(\alpha-\frac1d\right)\frac{F}{d}\right]$$
--   is $(n_A,n_B)$-extendible if and only if
--   $$\alpha\ \ge\ \min_{\lambda^{(A)}\vdash_dn_A,\ \lambda^{(B)}\vdash_dn_B}E^W(\lambda^{(A)},\lambda^{(B)}),\qquad E^W(\lambda^{(A)},\lambda^{(B)})=\frac{1}{2n_An_B}\left[c(\hat\lambda^{(AB)})-c(\lambda^{(A)})-c(\lambda^{(B)})\right]+\frac1d,$$
--   where $\hat\lambda^{(AB)}=\operatorname{sort}\{\lambda^{(A)}_i+\lambda^{(B)}_{d-i+1}\}$ and $c$ is the Casimir value of Eq. (9). Thus $\alpha_{n_A,n_B}=\min E^W$ over all pairs of $d$-partitions of $n_A$ and $n_B$.
--
--   This is the paper's necessary and sufficient condition for two-sided extendibility of Werner states, for every local dimension and every pair of extension sizes.
--
--   **Formalization Note** “$\alpha\ge\min E^W$” is written as the existence of a pair with $E^W\le\alpha$ (the set of pairs is finite and nonempty). Extendibility requires a positive semidefinite, trace-one extension whose marginal on every pair $(A_i,B_j)$ is $\rho^W(\alpha)$.
--
--   Differences from the source:
--   - correction: α_{nA,nB} = min over d̂ ∈ A ∩ [1, d−1] of E_W(λ̂^(A)(d̂), λ̂^(B)(d − d̂)) (Eq. (16), via Eq. (13), second equality, and Eq. (15)) → α_{nA,nB} = min of E_W over all pairs λ^A ⊢_d n_A, λ^B ⊢_d n_B (Eq. (13), first expression); reason: Eq. (16) is false: at d = 4, n_A = n_B = 3 exact diagonalization of H_W gives α = −5/9 while Eq. (16) gives −1/3 (Eq. (15) has a sign slip); and Eq. (13)'s restriction to the special pairs (14) fails at d = 5, n_A = n_B = 5, where λ^A = λ^B = (2, 2, 1, 0, 0) gives E_W = −11/25 (Lanczos: −0.44000) while the best special pair gives −2/5
--   - encoding: α ≥ min E_W over pairs of d-partitions → ∃ λ^A : DPart d n_A, ∃ λ^B : DPart d n_B, E_W(λ^A, λ^B) ≤ α; reason: equivalent for a finite nonempty set; avoids an infimum
--   - encoding: 1-based rows and sites → 0-based Fin d rows and Fin n sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, pp. 3–4, Eq. (12) and the first expression of Eq. (13), p. 4 ('In order obtain α_{nAnB}, we have to minimize E^W …'); printed headline p. 4, Eq. (16) (false)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

/-- Eqs. (12)–(13), pp. 3–4, corrected: the Werner state `ρ_W(α)`, `α ∈ [−1, 1]`, is
`(nA, nB)`-extendible iff `α ≥ min E_W(λ^A, λ^B)` over **all** pairs `λ^A ⊢_d nA`,
`λ^B ⊢_d nB`. (The paper's closed form, Eqs. (13)–(16), is false.) -/
theorem werner_extendibility (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB)
    (α : ℝ) (hα : α ∈ Set.Icc (-1 : ℝ) 1) :
    IsExtendible d nA nB (wernerState d α) ↔
      ∃ (lA : DPart d nA) (lB : DPart d nB), EW d nA nB lA.1 lB.1 ≤ α := by sorry

end WernerExt.TwoSided
