-- Prove2me | Theorems.Thm_TierneyMH_Reversibility_proposition1_symmetric_split
-- name    : TierneyMH.Reversibility.proposition1_symmetric_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T11:43:00.866163+00:00
-- url     : https://prove2.me/theorems/01b58ff8-3580-43a7-9550-7e562ab1b6cd
-- title:
--   Proposition 1: symmetric decomposition of a $\sigma$-finite measure on $E\times E$ against its transpose
-- statement:
--   Let $\mu$ be a $\sigma$-finite measure on the product space $(E\times E,\mathcal E\otimes\mathcal E)$ and let $\mu^T(dx,dy)=\mu(dy,dx)$. Then:
--
--   1. **Existence.** There is a symmetric set $R\in\mathcal E\otimes\mathcal E$ such that $\mu$ and $\mu^T$ are mutually absolutely continuous on $R$ and mutually singular on $R^c$.
--   2. **Uniqueness.** If $R$ and $R'$ both have these properties, then their symmetric difference is null for both measures:
--
--   $$\mu(R\,\triangle\,R')=0\quad\text{and}\quad \mu^T(R\,\triangle\,R')=0.$$
--
--   3. **Density.** For every such $R$ there is a version $r$ of the density $r(x,y)=\mu_R(dx,dy)/\mu^T_R(dx,dy)$ with $0<r(x,y)<\infty$ and $r(x,y)=1/r(y,x)$ for all $x,y\in E$.
--
--   This decomposition, applied to $\mu(dx,dy)=\pi(dx)Q(x,dy)$, supplies the set $R$ and the function $r$ in which Theorem 2's conditions are stated; its existence part guarantees that Theorem 2 is not vacuous.
--
--   **Formalization Note** The set conditions are the definition `IsSymmetricSplit` and the density conditions `IsRatioVersion`; $\mu^T$ is `μ.map Prod.swap`.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 2, Proposition 1

import Mathlib
import Definitions.Def_TierneyMH_Shared_IsSymmetricSplit
import Definitions.Def_TierneyMH_Shared_IsRatioVersion

open TierneyMH.Shared

open MeasureTheory
open scoped ENNReal

namespace TierneyMH.Reversibility

/-- **Proposition 1** (Tierney 1998, p. 2). Let `μ` be a σ-finite measure on `E × E` (with the
product σ-algebra) and `μᵀ = μ.map Prod.swap`. Then
1. there is a symmetric measurable set `R` on which `μ` and `μᵀ` are mutually absolutely
   continuous and on whose complement they are mutually singular;
2. such an `R` is unique up to sets null for both `μ` and `μᵀ`;
3. for such an `R`, the density `r = dμ_R / dμᵀ_R` has a version with `0 < r < ∞` and
   `r(x, y) = 1 / r(y, x)` for all `x, y`. -/
theorem proposition1_symmetric_split {E : Type*} [MeasurableSpace E]
    (μ : Measure (E × E)) [SigmaFinite μ] :
    (∃ R, IsSymmetricSplit μ R) ∧
    (∀ R R', IsSymmetricSplit μ R → IsSymmetricSplit μ R' →
      μ (symmDiff R R') = 0 ∧ (μ.map Prod.swap) (symmDiff R R') = 0) ∧
    (∀ R, IsSymmetricSplit μ R → ∃ r : E × E → ℝ≥0∞, IsRatioVersion μ R r) := by sorry

end TierneyMH.Reversibility
