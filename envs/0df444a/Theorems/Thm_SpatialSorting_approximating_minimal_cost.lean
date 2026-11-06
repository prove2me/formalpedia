-- Prove2me | Theorems.Thm_SpatialSorting_approximating_minimal_cost
-- name    : SpatialSorting.approximating_minimal_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:56:34.532867+00:00
-- url     : https://prove2.me/theorems/01004bcd-dd87-4dfd-aad8-671a54976e7a
-- title:
--   Lemma 5.7 — approximating the minimal cost
-- statement:
--   Fix $q\ge2$, $0<a\le b$, a smooth cutoff $\chi$, a density vector $\rho$ and $\alpha>1$. For sufficiently large $\beta$, and then sufficiently large $L$ (which may also depend on $\alpha$ and $\beta$), every cost matrix with $A_{\min}=a$, $A_{\max}=b$ satisfies
--
--   $$\mathcal H(\mathcal O_\beta)\le\alpha H(\sigma^L_\rho),\tag{26}$$
--
--   where $\mathcal O_\beta=\Gamma(\sigma^L_{\rho^{\langle\beta\rangle}})$ is the contour set of a minimal-cost configuration at the adjusted density $\rho^{\langle\beta\rangle}=\Theta^{-1}\rho$ (computed at the coexistence field), and $H(\sigma^L_\rho)=H_*(L,\rho)$ is the minimal energy at the prescribed density.
--
--   The density adjustment is exponentially small in $\beta$, and the lemma shows it changes the minimal interfacial cost only by a factor arbitrarily close to $1$.
--
--   Differences from the source:
--   - generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ; reason: every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity
--   - encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal); reason: past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β
--   - encoding: the optimal contour set 𝒪_β = Γ(σ^L_{ρ⟨β⟩}) for an arbitrary but fixed minimizer → Γ(σ') for every minimal-cost configuration σ' at the adjusted density Θ⁻¹ρ; reason: Definition 5.6 fixes an arbitrary choice and the bounds hold for any choice (p.31)
--   - encoding: H(σ^L_ρ) → H_*(L, ρ), the minimum energy over Ω_{Λ^L,ρ}; reason: the energy of a minimal-cost configuration is the minimum (Definitions 1.1 and 5.5)
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 5.7, p. 31 (PDF p. 32)

import Mathlib
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_IsDensity
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_Hstar
import Definitions.Def_SpatialSorting_cost
import Definitions.Def_SpatialSorting_contourSet
import Definitions.Def_SpatialSorting_IsCutoff
import Definitions.Def_SpatialSorting_adjusted
import Definitions.Def_SpatialSorting_IsCoexistenceField
import Definitions.Def_SpatialSorting_IsMinimal
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 5.7 — approximating the minimal cost.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 5.7, p. 31 (PDF p. 32).

Formalization Notes:
- generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ. Every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity.
- encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal). Past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β.
- encoding: the optimal contour set 𝒪_β = Γ(σ^L_{ρ⟨β⟩}) for an arbitrary but fixed minimizer → Γ(σ') for every minimal-cost configuration σ' at the adjusted density Θ⁻¹ρ. Definition 5.6 fixes an arbitrary choice and the bounds hold for any choice (p.31).
- encoding: H(σ^L_ρ) → H_*(L, ρ), the minimum energy over Ω_{Λ^L,ρ}. The energy of a minimal-cost configuration is the minimum (Definitions 1.1 and 5.5). -/
theorem approximating_minimal_cost :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ρ : Fin q → ℝ, IsDensity ρ → ∀ α : ℝ, 1 < α →
        ∃ β0 : ℝ, ∀ β : ℝ, β0 ≤ β → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
          ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A → amin A = a → amax A = b →
            ∀ h : Fin q → ℝ, IsCoexistenceField A χ β h →
              ∀ σ' : Coloring q L, IsMinimal A (adjusted A χ β h ρ) L σ' →
                ∑ γ ∈ contourSet σ', cost A γ ≤ α * Hstar A ρ L := by sorry

end SpatialSorting
