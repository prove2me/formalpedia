-- Prove2me | Theorems.Thm_ProperHalfspace_proposition_9
-- name    : ProperHalfspace.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:48.262123+00:00
-- url     : https://prove2.me/theorems/7af5bc02-76ce-4a37-bbbb-854f1baae5e6
-- title:
--   Proposition 9 — the critical-index dichotomy
-- statement:
--   There is a universal constant $C_{\mathrm{crit}}\ge1$ such that the following holds. Let $\tau,\nu\in(0,1/2)$, let $w\in\mathbb R^m$ have coordinates ordered by decreasing absolute value, let
--   $$K=\bigl\lceil C_{\mathrm{crit}}\tau^{-2}\log(1/\nu)\Lambda_\nu\bigr\rceil,$$
--   and let $\ell$ be the $\tau$-critical index of $w$.
--
--   1. If $\ell\le\min\{K,m\}$, the tail after the first $\ell$ coordinates is zero or $\tau$-regular.
--   2. Otherwise $K<m$, and truncation to the first $K$ coordinates satisfies
--   $$\sup_{\theta\in\mathbb R}\Pr_{x\sim\{\pm1\}^m}\Bigl[\operatorname{sign}(w\cdot x-\theta)\ne\operatorname{sign}\Bigl(\sum_{i=1}^Kw_ix_i-\theta\Bigr)\Bigr]\le\nu.$$
--
--   A halfspace is thus either regular after few coordinates, or essentially determined by few coordinates.
--
--   Differences from the source:
--   - encoding: sup over θ of a probability ≤ ν → ∀ θ, probability ≤ ν; reason: equivalent
--   - encoding: 1-based coordinates, first K coordinates → 0-based coordinates, i < K; reason: a relabelling
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Proposition 9, p.16; via O'Donnell, Servedio, Tan 2022, Lemma A.3

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace
import Definitions.Def_ProperHalfspace_Regularity

namespace ProperHalfspace

/-- Proposition 9, p.16 (critical-index dichotomy), via [OST22, Lemma A.3]. De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344
(Nov. 1, 2026). There is a universal `C_crit ≥ 1` such that for `τ, ν ∈ (0, 1/2)`, `w ∈ ℝᵐ` ordered by decreasing absolute value,
`K = ⌈C_crit τ⁻² log(1/ν) Λ_ν⌉` and `ℓ` the `τ`-critical index of `w`: if `ℓ ≤ min{K, m}`, the tail after the first `ℓ` coordinates
is zero or `τ`-regular; otherwise `K < m` and truncation to the first `K` coordinates changes `sign(w · x − θ)` with probability
at most `ν`, for every `θ`.

**Formalization Note.** `sup_θ … ≤ ν` is `∀ θ, … ≤ ν`. Coordinates are 0-based, so the first `K` coordinates are `i < K`. `IsRegular`
counts the zero vector as regular. -/
theorem proposition_9 : ∃ Ccrit : ℝ, 1 ≤ Ccrit ∧ ∀ τ ν : ℝ, 0 < τ → τ < 1 / 2 → 0 < ν → ν < 1 / 2 →
    ∀ (m : ℕ) (w : Fin m → ℝ), Antitone (fun i => |w i|) →
    let K : ℕ := ⌈Ccrit * τ⁻¹ ^ 2 * Real.log (1 / ν) * lam ν⌉₊
    let ℓ : ℕ := criticalIndex τ w
    (ℓ ≤ min K m → IsRegular τ (fun j : {j : Fin m // ℓ ≤ (j : ℕ)} => w j)) ∧
    (¬ ℓ ≤ min K m → K < m ∧ ∀ θ : ℝ,
      cubeProb (fun x : Cube m => sgn (∑ i, w i * coord x i - θ) ≠
        sgn (∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < K), w i * coord x i - θ)) ≤ ν) := by sorry

end ProperHalfspace
