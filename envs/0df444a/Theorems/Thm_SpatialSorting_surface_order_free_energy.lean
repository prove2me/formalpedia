-- Prove2me | Theorems.Thm_SpatialSorting_surface_order_free_energy
-- name    : SpatialSorting.surface_order_free_energy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:54:14.635857+00:00
-- url     : https://prove2.me/theorems/38dc7fe0-e409-44dc-a172-9dc0ed0e1e26
-- title:
--   Lemma 4.6 — surface-order free energy of restricted regions
-- statement:
--   Fix $q\ge2$, $0<a\le b$ and a smooth cutoff $\chi$. There are $c_0\in(0,a/64]$, $C$ and $\beta_0$ such that for every rate $c_*\in(0,c_0]$ ($\tau_\beta=c_*\beta$, $\ell_0=1$), every $\beta\ge\beta_0$ and every cost matrix $A$ with $A_{\min}=a$, $A_{\max}=b$ the following holds. Let $\mathbf h^*_\beta$ be the coexistence field and $p_\beta$ the common value of the truncated pressures at $\mathbf h^*_\beta$. For every $L$, every colour $j$ and every finite $V\subseteq D_L$ (possibly disconnected, with holes, or touching the collar),
--
--   $$\bigl|\log Z^L_j(\beta,\mathbf h^*_\beta,V)-p_\beta|V|\bigr|\le C\,|\partial_{\rm ext}V|_\Sigma\,e^{-\tau_\beta\ell_0/8},\tag{21}$$
--
--   where $|\partial_{\rm ext}V|_\Sigma=\sum_k|\partial_{\rm ext}V_k|$ over the connected components $V_k$ of $V$. In particular, for every scaffold $\mathcal S$ with complementary components $V_k$ and labels $j_k$,
--
--   $$\sum_k\bigl|\log Z^L_{j_k}(\beta,\mathbf h^*_\beta,V_k)-p_\beta|V_k|\bigr|\le C\bigl(6|\overline{\mathcal S}|+4L+4\bigr)e^{-\tau_\beta\ell_0/8}.\tag{22}$$
--
--   The restricted free energy of any region is bulk pressure times volume up to an error of the order of its boundary, with no term proportional to the area of a hole.
--
--   Differences from the source:
--   - generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ; reason: every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity
--   - generalization: τ_β = c*β with 0 < c* ≤ A_min/64 chosen sufficiently small, ℓ_0 = 1 → the bound holds for every c* in (0, c_0] for some c_0 ∈ (0, A_min/64], with the β-threshold independent of c*; reason: the bound weakens as c* decreases, which is what 'chosen sufficiently small' allows; ℓ_0 = 1 as on p.24
--   - encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal); reason: past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β
--   - encoding: p_β, the common value of the truncated pressures at h*_β → any real p with ψ̂_j(h) = p for every colour j; reason: the common value is determined by the field
--   - encoding: the labels j_k of the complementary components → every labelling lab : Finset (ℤ × ℤ) → Fin q satisfying (W3) and j_0 = 0 (IsLabeling L 𝒮 lab); reason: the labels of the complementary components of a scaffold are determined by (W3), so every such labelling gives the page's labels
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.6, p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_supp
import Definitions.Def_SpatialSorting_extBdrySum
import Definitions.Def_SpatialSorting_Zres
import Definitions.Def_SpatialSorting_comps
import Definitions.Def_SpatialSorting_IsLabeling
import Definitions.Def_SpatialSorting_IsScaffold
import Definitions.Def_SpatialSorting_IsCutoff
import Definitions.Def_SpatialSorting_pressure
import Definitions.Def_SpatialSorting_IsCoexistenceField
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 4.6 — surface-order free energy of restricted regions.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.6, p. 27 (PDF p. 28).

Formalization Notes:
- generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ. Every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity.
- generalization: τ_β = c*β with 0 < c* ≤ A_min/64 chosen sufficiently small, ℓ_0 = 1 → the bound holds for every c* in (0, c_0] for some c_0 ∈ (0, A_min/64], with the β-threshold independent of c*. The bound weakens as c* decreases, which is what 'chosen sufficiently small' allows; ℓ_0 = 1 as on p.24.
- encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal). Past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β.
- encoding: p_β, the common value of the truncated pressures at h*_β → any real p with ψ̂_j(h) = p for every colour j. The common value is determined by the field.
- encoding: the labels j_k of the complementary components → every labelling lab : Finset (ℤ × ℤ) → Fin q satisfying (W3) and j_0 = 0 (IsLabeling L 𝒮 lab). The labels of the complementary components of a scaffold are determined by (W3), so every such labelling gives the page's labels. -/
theorem surface_order_free_energy :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ χ : ℝ → ℝ, IsCutoff χ →
        ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ a / 64 ∧ ∃ C β0 : ℝ,
          ∀ cstar : ℝ, 0 < cstar → cstar ≤ c0 → ∀ β : ℝ, β0 ≤ β →
            ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A → amin A = a → amax A = b →
              ∀ (h : Fin q → ℝ) (p : ℝ), IsCoexistenceField A χ β h →
                (∀ j, pressure A χ β j h = p) → ∀ L : ℕ,
                  (∀ (j : Fin q) (V : Finset (ℤ × ℤ)), V ⊆ D L →
                    |Real.log (Zres A β h j V) - p * (V.card : ℝ)| ≤
                      C * (extBdrySum V : ℝ) * Real.exp (-(cstar * β) / 8)) ∧
                  ∀ (S : Finset (Contour q)) (lab : Finset (ℤ × ℤ) → Fin q),
                    IsScaffold L S → IsLabeling L S lab →
                    ∑ V ∈ comps L S, |Real.log (Zres A β h (lab V) V) - p * (V.card : ℝ)| ≤
                      C * (6 * ((supp S).card : ℝ) + 4 * (L : ℝ) + 4) *
                        Real.exp (-(cstar * β) / 8) := by sorry

end SpatialSorting
