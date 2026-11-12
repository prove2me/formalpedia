-- Prove2me | Theorems.Thm_SampleRemoval_sFrac_attained
-- name    : SampleRemoval.sFrac_attained
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T05:21:24.584363+00:00
-- url     : https://prove2.me/theorems/41c5aa4d-bbcb-4826-817e-3b2de7914ac8
-- title:
--   Theorem 3.3 (More generally) — $s_{\mathrm{frac}}$ is attained when $n-s_{\mathrm{frac}}>d-1$
-- statement:
--   Assume the design is in general position, and let $\mathcal W$ be the nonempty feasible set of a pair $(e,\theta)$, with fractional stability $s_{\mathrm{frac}}=\inf\{n-\|w\|_1:w\in\mathcal W\}$. If
--
--   $$
--   n-s_{\mathrm{frac}}>d-1,
--   $$
--
--   then the infimum is attained: there is $w\in\mathcal W$ with $n-\|w\|_1=s_{\mathrm{frac}}$.
--
--   This is the final sentence of Theorem 3.3. Attainment is what allows the rounding of Theorem 3.3 to be applied to an optimal fractional solution, which yields the bound $s_{\mathrm{int}}<s_{\mathrm{frac}}+d$.
--
--   Differences from the source:
--
--   - encoding: observations (x_i, y_i) ∈ ℝᵈ × ℝ indexed by i ∈ [n] → x : Fin n → Fin d → ℝ, y : Fin n → ℝ, paper index i = Lean index i − 1; reason: Lean convention; same instances
--   - encoding: ∥w∥₁ → ∑ i, w i; reason: every weight lies in [0, 1], so the sum of the coordinates is the ℓ¹ norm
--   - encoding: inf over 𝒲 (= +∞ when 𝒲 = ∅, so the hypothesis n − s_frac > d − 1 fails there) → hypothesis 𝒲.Nonempty; reason: Lean's sInf ∅ = 0; the hypothesis excludes only the case where the source's hypothesis already fails
--   - generalization: (e, θ) is a target, ⟨e, β([n])⟩ > θ (§2, Audits) → (e, θ) ∈ ℝᵈ × ℝ arbitrary; reason: the statement and its proof do not use the target condition; taking a target specializes to the source's claim
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 3.3, p.5 (PDF p.7), last sentence; proof paragraph "Attainment."

import Mathlib
import Definitions.Def_SampleRemoval_feasible
import Definitions.Def_SampleRemoval_sFrac
import Definitions.Def_SampleRemoval_GeneralPosition

set_option autoImplicit false

namespace SampleRemoval

/-- **Theorem 3.3, "More generally"** (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), p.5; proof paragraph "Attainment."): "More generally,
s_frac is attained whenever n − s_frac > d − 1."

Assume GP and that `𝒲` is nonempty. If `n − s_frac > d − 1`, then some `w ∈ 𝒲` has
`n − ∥w∥₁ = s_frac`.

**Formalization Note** `𝒲.Nonempty` is assumed because Lean's `sInf ∅ = 0`, while the paper's
infimum over `∅` is `+∞` and its hypothesis `n − s_frac > d − 1` already fails there. The pair
`(e, θ)` is arbitrary: the target condition `⟨e, β([n])⟩ > θ` is not assumed. -/
theorem sFrac_attained {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) (hGP : GeneralPosition x) (hne : (feasible x y e θ).Nonempty)
    (h : (d : ℝ) - 1 < n - sFrac x y e θ) :
    ∃ w ∈ feasible x y e θ, (n : ℝ) - ∑ i, w i = sFrac x y e θ := by sorry

end SampleRemoval
