-- Prove2me | Theorems.Thm_SpatialSorting_surface_order_minimal_cost
-- name    : SpatialSorting.surface_order_minimal_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:45:59.059251+00:00
-- url     : https://prove2.me/theorems/9ccba529-60ac-47ad-ab65-8bda045a05f5
-- title:
--   Lemma 5.8 — surface-order minimal cost
-- statement:
--   Fix $q\ge2$. There is a threshold function $L_{\rm thr}$ of $\rho_{\min}$ alone such that for all $0<a\le b$ there is $b_0=b_0(q,a,b)\ge1$ with the following property: for every cost matrix $A$ with $A_{\min}=a$, $A_{\max}=b$, every density vector $\rho$, every $L\ge L_{\rm thr}(\rho_{\min})$ and every minimal-cost configuration $\sigma^L_\rho$ of $\Lambda^L$ with density $\rho$,
--
--   $$\frac{\sqrt{\rho_{\min}}}{b_0}\le\frac{H(\sigma^L_\rho)}{L}\le b_0,\qquad\frac{\sqrt{\rho_{\min}}}{b_0}\le\frac{|\overline\Gamma(\sigma^L_\rho)|}{L}\le b_0.\tag{27}$$
--
--   The lower threshold on $L$ may depend on $\rho_{\min}$ and $q$, but the constant $b_0$ does not. The benchmark $H_*(L,\rho)$ of the Sorted event is therefore of order $L$, the square root of the number of sites.
--
--   Differences from the source:
--   - encoding: H(σ^L_ρ) and |Γ̄(σ^L_ρ)| for an arbitrary but fixed minimal-cost configuration → the four bounds for every minimal-cost configuration σ, with |Γ̄(σ)| the size of the support of its contour set; reason: Definition 5.5 fixes an arbitrary minimizer; the bounds hold for each
--   - encoding: 'for all sufficiently large L … The lower threshold on L may depend on ρ_min and q' → a threshold L_thr(ρ_min) chosen after q and before A_min, A_max, b; reason: quantifier order expresses the last sentence of the lemma
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 5.8, p. 31 (PDF p. 32)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_IsDensity
import Definitions.Def_SpatialSorting_rhoMin
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_supp
import Definitions.Def_SpatialSorting_contourSet
import Definitions.Def_SpatialSorting_IsMinimal
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 5.8 — surface-order minimal cost.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 5.8, p. 31 (PDF p. 32).

Formalization Notes:
- encoding: H(σ^L_ρ) and |Γ̄(σ^L_ρ)| for an arbitrary but fixed minimal-cost configuration → the four bounds for every minimal-cost configuration σ, with |Γ̄(σ)| the size of the support of its contour set. Definition 5.5 fixes an arbitrary minimizer; the bounds hold for each.
- encoding: 'for all sufficiently large L … The lower threshold on L may depend on ρ_min and q' → a threshold L_thr(ρ_min) chosen after q and before A_min, A_max, b. Quantifier order expresses the last sentence of the lemma. -/
theorem surface_order_minimal_cost :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∃ Lthr : ℝ → ℕ, ∀ a b : ℝ, 0 < a → a ≤ b →
      ∃ b0 : ℝ, 1 ≤ b0 ∧
        ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A → amin A = a → amax A = b →
          ∀ ρ : Fin q → ℝ, IsDensity ρ → ∀ L : ℕ, Lthr (rhoMin ρ) ≤ L →
            ∀ σ : Coloring q L, IsMinimal A ρ L σ →
              Real.sqrt (rhoMin ρ) / b0 ≤ HV A (D L) (extendBy 0 (I L) σ) / L ∧
              HV A (D L) (extendBy 0 (I L) σ) / L ≤ b0 ∧
              Real.sqrt (rhoMin ρ) / b0 ≤ ((supp (contourSet σ)).card : ℝ) / L ∧
              ((supp (contourSet σ)).card : ℝ) / L ≤ b0 := by sorry

end SpatialSorting
