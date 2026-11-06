-- Prove2me | Theorems.Thm_SpatialSorting_grand_canonical_comparison
-- name    : SpatialSorting.grand_canonical_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:55:28.310313+00:00
-- url     : https://prove2.me/theorems/46375469-447e-41d6-be2d-2cafb224901b
-- title:
--   Lemma 7.1 — grand canonical comparison
-- statement:
--   Fix $q\ge2$, $0<a\le b$, a smooth cutoff $\chi$, a density vector $\rho$ and $\alpha'>1$. For sufficiently large $\beta$ and then $L$, for every cost matrix with $A_{\min}=a$, $A_{\max}=b$, at the coexistence field $\mathbf h^*_\beta$, every scaffold $\mathcal S$ with $\mathcal H(\mathcal S)\ge\alpha'\mathcal H(\mathcal O_\beta)$ satisfies
--
--   $$\frac{Z^L_{\mathcal S}}{Z^L_{\mathcal O_\beta}}\le\exp\Bigl[-\frac\beta2\,\frac{\alpha'-1}{\alpha'}\,\mathcal H(\mathcal S)\Bigr].$$
--
--   Here $\mathcal O_\beta$ is the contour set of a minimal-cost configuration at the adjusted density and $Z^L_{\mathcal S}$ the contour-restricted grand canonical partition function of $\mathcal S$. A scaffold whose cost exceeds the optimal one by a factor $\alpha'$ is exponentially suppressed in its cost.
--
--   Differences from the source:
--   - generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ; reason: every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity
--   - encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal); reason: past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β
--   - encoding: the optimal contour set 𝒪_β = Γ(σ^L_{ρ⟨β⟩}) for an arbitrary but fixed minimizer → Γ(σ') for every minimal-cost configuration σ' at the adjusted density Θ⁻¹ρ; reason: Definition 5.6 fixes an arbitrary choice and the bounds hold for any choice (p.31)
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.1, p. 41 (PDF p. 42)

import Mathlib
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_IsDensity
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_cost
import Definitions.Def_SpatialSorting_IsScaffold
import Definitions.Def_SpatialSorting_contourSet
import Definitions.Def_SpatialSorting_ZS
import Definitions.Def_SpatialSorting_IsCutoff
import Definitions.Def_SpatialSorting_adjusted
import Definitions.Def_SpatialSorting_IsCoexistenceField
import Definitions.Def_SpatialSorting_IsMinimal
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 7.1 — grand canonical comparison.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.1, p. 41 (PDF p. 42).

Formalization Notes:
- generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ. Every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity.
- encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal). Past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β.
- encoding: the optimal contour set 𝒪_β = Γ(σ^L_{ρ⟨β⟩}) for an arbitrary but fixed minimizer → Γ(σ') for every minimal-cost configuration σ' at the adjusted density Θ⁻¹ρ. Definition 5.6 fixes an arbitrary choice and the bounds hold for any choice (p.31). -/
theorem grand_canonical_comparison :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ρ : Fin q → ℝ, IsDensity ρ → ∀ α' : ℝ, 1 < α' →
        ∃ β0 : ℝ, ∀ β : ℝ, β0 ≤ β → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
          ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A → amin A = a → amax A = b →
            ∀ h : Fin q → ℝ, IsCoexistenceField A χ β h →
              ∀ σ' : Coloring q L, IsMinimal A (adjusted A χ β h ρ) L σ' →
                ∀ S : Finset (Contour q), IsScaffold L S →
                  α' * ∑ γ ∈ contourSet σ', cost A γ ≤ ∑ γ ∈ S, cost A γ →
                  ZS A β h L S / ZS A β h L (contourSet σ') ≤
                    Real.exp (-(β / 2) * ((α' - 1) / α') * ∑ γ ∈ S, cost A γ) := by sorry

end SpatialSorting
