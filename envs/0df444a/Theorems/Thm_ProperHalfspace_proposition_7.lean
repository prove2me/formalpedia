-- Prove2me | Theorems.Thm_ProperHalfspace_proposition_7
-- name    : ProperHalfspace.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:09.824056+00:00
-- url     : https://prove2.me/theorems/e6ef2c03-2dbe-4208-9ff2-14d116a51b4f
-- title:
--   Proposition 7 — multilinear and geometric extensions of a regular halfspace are close
-- statement:
--   There is a universal constant $C$ such that the following holds. Let $h(x)=\operatorname{sign}(w\cdot x-\theta)$, with geometric extension $h_G(z)=\operatorname{sign}(w\cdot z-\theta)$ and multilinear extension $\tilde h$.
--
--   1. If $h$ is $\tau$-regular with $\tau\in(0,1]$, then
--   $$\mathbf E_{z\sim N(0,I_n)}\bigl[(\tilde h(z)-h_G(z))^2\bigr]\le C\tau^{1/2}.$$
--   2. If $\|w\|_2=1$ and $\beta_w=(\sum_iw_i^4)^{1/2}$, then $\|\tilde h-h_G\|^2_{L^2(N(0,I_n))}\le C\beta_w^{1/2}$.
--
--   This is the bridge between Boolean and Gaussian correlations for regular halfspaces.
--
--   Differences from the source:
--   - encoding: clause 2 sits in the setting of a τ-regular h → clause 2 has no regularity hypothesis; reason: every w is 1-regular, so the page's setting excludes nothing
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Proposition 7, p.15 (restated p.38)

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace
import Definitions.Def_ProperHalfspace_Gaussian
import Definitions.Def_ProperHalfspace_Regularity
import Definitions.Def_ProperHalfspace_ExpComparison

open MeasureTheory

namespace ProperHalfspace

/-- Proposition 7, p.15 (closeness of multilinear and geometric extensions for regular halfspaces). De, Mossel, Nadimpalli,
Neeman, arXiv:2611.02344 (Nov. 1, 2026). With one universal `C`: if `h = sign(w · x − θ)` is `τ`-regular, `τ ∈ (0, 1]`, then
`E[(h̃ − h_G)²] ≤ C τ^{1/2}`; and if `‖w‖₂ = 1`, with no regularity assumed, then `E[(h̃ − h_G)²] ≤ C β_w^{1/2}`. -/
theorem proposition_7 : ∃ C : ℝ, ∀ (n : ℕ) (w : Fin n → ℝ) (θ : ℝ),
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 → IsRegular τ w →
      ∫ z, (mlExt (ltf w θ) z - ltfG w θ z) ^ 2 ∂stdGauss n ≤ C * τ ^ (1 / 2 : ℝ)) ∧
    (∑ i, w i ^ 2 = 1 →
      ∫ z, (mlExt (ltf w θ) z - ltfG w θ z) ^ 2 ∂stdGauss n ≤ C * betaW w ^ (1 / 2 : ℝ)) := by sorry

end ProperHalfspace
