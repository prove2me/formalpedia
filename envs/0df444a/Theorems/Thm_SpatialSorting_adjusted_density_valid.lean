-- Prove2me | Theorems.Thm_SpatialSorting_adjusted_density_valid
-- name    : SpatialSorting.adjusted_density_valid
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:56:25.198718+00:00
-- url     : https://prove2.me/theorems/9e72a6e7-7ff5-40e9-8887-534f32a687bc
-- title:
--   Lemma 5.3 — validity of the adjusted density
-- statement:
--   Fix $q\ge2$, $0<a\le b$ and a smooth cutoff $\chi$. There is $c_0\in(0,a/64]$ such that for every density vector $\rho$ there is $\beta_0$ with the following property. For every rate $c_*\in(0,c_0]$, every $\beta\ge\beta_0$, every cost matrix with $A_{\min}=a$, $A_{\max}=b$, and the coexistence field $\mathbf h^*_\beta$, set $\varepsilon_\beta=e^{-\tau_\beta\ell_0/4}$ with $\tau_\beta=c_*\beta$, $\ell_0=1$. Then the phase-density matrix $\Theta=(\partial_{h_i}\widehat\psi_j(\mathbf h^*_\beta))_{i,j}$ is column stochastic (nonnegative entries, $\sum_i\theta_{i,j}=1$) and invertible, and
--
--   $$\rho^{\langle\beta\rangle}=\Theta^{-1}\rho\in\Delta_{q-1},\qquad\|\rho^{\langle\beta\rangle}-\rho\|_1\le4\varepsilon_\beta.\tag{24}$$
--
--   In particular, $\min_i\rho^{\langle\beta\rangle}_i\ge\rho_{\min}/2$ once $4\varepsilon_\beta\le\rho_{\min}/2$.
--
--   The adjusted density is the vector of phase volumes that reproduces the prescribed colour densities after the thermal defects of each phase are accounted for; the lemma shows it is a genuine density vector close to $\rho$.
--
--   Differences from the source:
--   - generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ; reason: every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity
--   - generalization: τ_β = c*β with 0 < c* ≤ A_min/64 chosen sufficiently small, ℓ_0 = 1 → the bound holds for every c* in (0, c_0] for some c_0 ∈ (0, A_min/64], with the β-threshold independent of c*; reason: the bound weakens as c* decreases, which is what 'chosen sufficiently small' allows; ℓ_0 = 1 as on p.24
--   - encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal); reason: past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β
--   - reading: 'For sufficiently large β' (Lemma 5.3) → the threshold β0 may depend on ρ; reason: Θ⁻¹ρ ∈ Δ_{q−1} needs the perturbation 4ε_β to be small relative to ρ_min (proof, p.30), so no threshold uniform in ρ exists; column stochasticity and invertibility hold at the same threshold
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 5.3, p. 29 (PDF p. 30)

import Mathlib
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_IsDensity
import Definitions.Def_SpatialSorting_rhoMin
import Definitions.Def_SpatialSorting_IsCutoff
import Definitions.Def_SpatialSorting_theta
import Definitions.Def_SpatialSorting_adjusted
import Definitions.Def_SpatialSorting_IsCoexistenceField
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 5.3 — validity of the adjusted density.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 5.3, p. 29 (PDF p. 30).

Formalization Notes:
- generalization: thresholds and constants that may depend on the cost matrix A ('for sufficiently large β'; Lemmas 4.3, 4.6, 6.1 print β0(q, A), C(q, A)), for the paper's one fixed cutoff χ → the constants are chosen from (q, A_min, A_max, χ) before the cost matrix, for every admissible cutoff χ. Every estimate of §§4–7 and Appendices A–C uses A only through A_min ≤ A(i, j) ≤ A_max for i ≠ j, and the paper's χ is one admissible cutoff, so the statement specializes to the printed one; Theorem 1 needs this uniformity.
- generalization: τ_β = c*β with 0 < c* ≤ A_min/64 chosen sufficiently small, ℓ_0 = 1 → the bound holds for every c* in (0, c_0] for some c_0 ∈ (0, A_min/64], with the β-threshold independent of c*. The bound weakens as c* decreases, which is what 'chosen sufficiently small' allows; ℓ_0 = 1 as on p.24.
- encoding: the coexistence field h*_β of Lemma 4.3 → any field h with IsCoexistenceField A χ β h (in (−1, 1)^q, h_0 = 0, all truncated pressures equal). Past the threshold of Lemma 4.3 such a field is unique (T_i = r_0 − r_i is a contraction on the whole cube, Lemma C.3, Eq. (54), Lemma B.2), so it is h*_β.
- reading: 'For sufficiently large β' (Lemma 5.3) → the threshold β0 may depend on ρ. Θ⁻¹ρ ∈ Δ_{q−1} needs the perturbation 4ε_β to be small relative to ρ_min (proof, p.30), so no threshold uniform in ρ exists; column stochasticity and invertibility hold at the same threshold. -/
theorem adjusted_density_valid :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ χ : ℝ → ℝ, IsCutoff χ →
        ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ a / 64 ∧
          ∀ ρ : Fin q → ℝ, IsDensity ρ → ∃ β0 : ℝ,
            ∀ cstar : ℝ, 0 < cstar → cstar ≤ c0 → ∀ β : ℝ, β0 ≤ β →
              ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A → amin A = a → amax A = b →
                ∀ h : Fin q → ℝ, IsCoexistenceField A χ β h →
                  let ε := Real.exp (-(cstar * β) / 4)
                  (∀ i j, 0 ≤ theta A χ β h i j) ∧ (∀ j, ∑ i, theta A χ β h i j = 1) ∧
                  IsUnit (theta A χ β h).det ∧
                  IsDensity (adjusted A χ β h ρ) ∧
                  ∑ i, |adjusted A χ β h ρ i - ρ i| ≤ 4 * ε ∧
                  (4 * ε ≤ rhoMin ρ / 2 → ∀ i, rhoMin ρ / 2 ≤ adjusted A χ β h ρ i) := by sorry

end SpatialSorting
