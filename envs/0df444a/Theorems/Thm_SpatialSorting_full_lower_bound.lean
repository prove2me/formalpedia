-- Prove2me | Theorems.Thm_SpatialSorting_full_lower_bound
-- name    : SpatialSorting.full_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:55:57.650283+00:00
-- url     : https://prove2.me/theorems/1a47165f-0e8a-416a-a8da-8b9c36e47f50
-- title:
--   Lemma 6.8 — full fixed-magnetization lower bound
-- statement:
--   Fix $q\ge2$. There is $C_q$ such that for all $0<a\le b$ and every smooth cutoff $\chi$ there is $c_0\in(0,a/64]$ with the following property. For every density vector $\rho$ there is $\beta_0$ such that for every rate $c_*\in(0,c_0]$ ($\tau_\beta=c_*\beta$, $\ell_0=1$) and $\beta\ge\beta_0$ there is $L_0$ such that for $L\ge L_0$ and every cost matrix with $A_{\min}=a$, $A_{\max}=b$,
--
--   $$Z^{\rm tot}_{\mathbf n}(\beta,\mathbf h^*_\beta)\ge(L+1)^{-C_q}\,Z^L_{\mathcal O_\beta}(\beta,\mathbf h^*_\beta)\,\exp\bigl[-\beta e^{-\tau_\beta\ell_0/24}|\overline{\mathcal O_\beta}|\bigr].\tag{37}$$
--
--   Here $Z^{\rm tot}_{\mathbf n}$ is the partition function of all configurations with the original prescribed counts $\mathbf n$ ($n_i=\lfloor\rho_iN_L\rfloor$ for $i\ge1$, $n_0$ the leftover), with no contour restriction, and $Z^L_{\mathcal O_\beta}$ is the contour-restricted grand canonical partition function defined by the scaffold $\mathcal O_\beta$, the contour set of a minimal-cost configuration at the adjusted density.
--
--   This is the canonical lower bound: restoring the exact counts costs only a polynomial factor and an exponentially small multiple of the scaffold size.
--
--   Differences from the source:
--   - generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ; reason: every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity
--   - generalization: τ_β = c*β with 0 < c* ≤ A_min/64 chosen sufficiently small, ℓ_0 = 1 → the bound holds for every c* in (0, c_0] for some c_0 ∈ (0, A_min/64], with the β-threshold independent of c*; reason: the bound weakens as c* decreases, which is what 'chosen sufficiently small' allows; ℓ_0 = 1 as on p.24
--   - encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal); reason: past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β
--   - encoding: the optimal contour set 𝒪_β = Γ(σ^L_{ρ⟨β⟩}) for an arbitrary but fixed minimizer → Γ(σ') for every minimal-cost configuration σ' at the adjusted density Θ⁻¹ρ; reason: Definition 5.6 fixes an arbitrary choice and the bounds hold for any choice (p.31)
--   - reading: the exponent C_q → C_q is chosen after q and before every other parameter; reason: the subscript and the proof (polynomial prefactor of 'degree depending only on q', Lemma 6.3, p.36)
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.8, p. 39 (PDF p. 40)

import Mathlib
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_IsDensity
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_supp
import Definitions.Def_SpatialSorting_contourSet
import Definitions.Def_SpatialSorting_ZS
import Definitions.Def_SpatialSorting_Ztot
import Definitions.Def_SpatialSorting_IsCutoff
import Definitions.Def_SpatialSorting_adjusted
import Definitions.Def_SpatialSorting_IsCoexistenceField
import Definitions.Def_SpatialSorting_IsMinimal
import Definitions.Def_SpatialSorting_nOf
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 6.8 — full fixed-magnetization lower bound.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.8, p. 39 (PDF p. 40).

Formalization Notes:
- generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ. Every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity.
- generalization: τ_β = c*β with 0 < c* ≤ A_min/64 chosen sufficiently small, ℓ_0 = 1 → the bound holds for every c* in (0, c_0] for some c_0 ∈ (0, A_min/64], with the β-threshold independent of c*. The bound weakens as c* decreases, which is what 'chosen sufficiently small' allows; ℓ_0 = 1 as on p.24.
- encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal). Past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β.
- encoding: the optimal contour set 𝒪_β = Γ(σ^L_{ρ⟨β⟩}) for an arbitrary but fixed minimizer → Γ(σ') for every minimal-cost configuration σ' at the adjusted density Θ⁻¹ρ. Definition 5.6 fixes an arbitrary choice and the bounds hold for any choice (p.31).
- reading: the exponent C_q → C_q is chosen after q and before every other parameter. The subscript and the proof (polynomial prefactor of 'degree depending only on q', Lemma 6.3, p.36). -/
theorem full_lower_bound :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∃ Cq : ℝ, ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ a / 64 ∧
        ∀ ρ : Fin q → ℝ, IsDensity ρ → ∃ β0 : ℝ,
          ∀ cstar : ℝ, 0 < cstar → cstar ≤ c0 → ∀ β : ℝ, β0 ≤ β → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
            ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A → amin A = a → amax A = b →
              ∀ h : Fin q → ℝ, IsCoexistenceField A χ β h →
                ∀ σ' : Coloring q L, IsMinimal A (adjusted A χ β h ρ) L σ' →
                  ((L : ℝ) + 1) ^ (-Cq) * ZS A β h L (contourSet σ') *
                      Real.exp (-β * Real.exp (-(cstar * β) / 24) *
                        ((supp (contourSet σ')).card : ℝ)) ≤
                    Ztot A β h L (nOf ρ L) := by sorry

end SpatialSorting
