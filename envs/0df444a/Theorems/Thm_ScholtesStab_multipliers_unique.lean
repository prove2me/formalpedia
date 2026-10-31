-- Prove2me | Theorems.Thm_ScholtesStab_multipliers_unique
-- name    : ScholtesStab.multipliers_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:00.107504+00:00
-- url     : https://prove2.me/theorems/2818a5ed-7b3f-4180-9c96-f2ddd54829cf
-- title:
--   Uniqueness of the MPCC multipliers under MPCC-LICQ
-- statement:
--   Let $\bar x\in M$ satisfy MPCC-LICQ. If two tuples $(\bar\sigma,\bar\varrho)$ and $(\bar\sigma',\bar\varrho')$ both satisfy the W-stationarity equation (5) at $\bar x$, then
--
--   $$
--   \bar\sigma_{1,j}=\bar\sigma'_{1,j}\ (j\in a_{01}(\bar x)),\qquad \bar\sigma_{2,j}=\bar\sigma'_{2,j}\ (j\in a_{10}(\bar x)),\qquad \bar\varrho_{i,j}=\bar\varrho'_{i,j}\ (j\in a_{00}(\bar x),\ i=1,2).
--   $$
--
--   This is what allows the paper to speak of *the* multipliers of a W-stationary point, and hence of its Lagrange function and C-index, under MPCC-LICQ.
--
--   Differences from the source:
--   - encoding: ℝⁿ, indices j = 1, …, κ → EuclideanSpace ℝ (Fin n), indices in Fin κ (0-based); reason: a relabelling of coordinates and indices; same instances
--   - encoding: f, F₁, F₂ twice continuously differentiable (standing assumption, p.1) → ContDiff ℝ 2 fields of the structure MPCC; reason: the standing assumption is carried by every instance; same instances
--   - encoding: differentials DF(x), Hessians D²L(x) → fderiv ℝ F x : ℝⁿ →L[ℝ] ℝ and fderiv ℝ (fderiv ℝ L) x as a bilinear form; reason: the Fréchet derivative of a C² function is its differential and its second derivative is the Hessian; linear independence of differentials is that of gradients
--   - encoding: multipliers σ̄₁,ⱼ (j ∈ a₀₁), σ̄₂,ⱼ (j ∈ a₁₀), ϱ̄₁,ⱼ, ϱ̄₂,ⱼ (j ∈ a₀₀) → total functions Fin κ → ℝ whose values outside these index sets are never used; reason: every formula and count ranges over the paper's index sets only; same instances
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.6 ("which are unique under MPCC-LICQ")

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_MPCCLICQ
import Definitions.Def_ScholtesStab_MPCC_IsCStationary

namespace ScholtesStab

open MPCC

/-- **Uniqueness of the MPCC multipliers under MPCC-LICQ.**
Lämmel–Shikhman, arXiv:2501.07383v2, p.6: "For a W-stationary point x̄ ∈ M with multipliers
(σ̄, ϱ̄) – which are unique under MPCC-LICQ – it is convenient to define the appropriate Lagrange
function as".

If `x̄ ∈ M` satisfies MPCC-LICQ and two multiplier tuples `m, m'` both satisfy the
W-stationarity equation (5) at `x̄`, then they agree on the index sets where the multipliers
live: `σ̄₁ = σ̄₁'` on `a₀₁(x̄)`, `σ̄₂ = σ̄₂'` on `a₁₀(x̄)`, and `ϱ̄ᵢ = ϱ̄ᵢ'` on `a₀₀(x̄)`.

**Formalization Note.** Multipliers are total functions `Fin κ → ℝ`; their values off the
relevant index sets are irrelevant and are not claimed to agree. -/
theorem multipliers_unique {n κ : ℕ} (P : MPCC n κ) (xbar : E n) (m m' : MPCCMult κ)
    (hxbar : xbar ∈ P.M) (hLICQ : P.MPCCLICQ xbar)
    (hm : P.StatEq xbar m) (hm' : P.StatEq xbar m') :
    P.SameMult xbar m m' := by sorry

end ScholtesStab
