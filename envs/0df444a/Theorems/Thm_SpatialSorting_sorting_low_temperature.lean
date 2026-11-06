-- Prove2me | Theorems.Thm_SpatialSorting_sorting_low_temperature
-- name    : SpatialSorting.sorting_low_temperature
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:47:28.02364+00:00
-- url     : https://prove2.me/theorems/0506aa94-f51b-44f0-91a5-90bd0c4fbda6
-- title:
--   Theorem 1 — sorting at low temperature
-- statement:
--   Let $q\ge2$ be a number of colours, $A\in\mathcal A_q$ a cost matrix (symmetric, zero diagonal, positive off-diagonal entries) and $\rho\in\Delta_{q-1}$ a density vector with all entries positive. Consider the fixed-magnetization Generalized Potts Model on the $L\times L$ rhombus $D_L$ of the triangular lattice, with its two-layer collar $B_L$ wired to colour $0$ and the free counts $|\{v\in I_L:\sigma_v=i\}|=\lfloor\rho_iN_L\rfloor$ for $i\ge1$ prescribed, and its Gibbs distribution $\pi_{\Lambda^L,\beta,\rho}(\sigma)\propto e^{-\beta H_{\Lambda^L}(\sigma)}$.
--
--   There is $c_s>0$ depending only on $q$, $A_{\min}$, $A_{\max}$ and $\rho_{\min}=\min_i\rho_i$ such that for every $\alpha>1$ and $\delta\in(0,1)$ there exist $\beta_0=\beta_0(\alpha,\delta,\rho,q,A_{\min},A_{\max})$ and $L_0=L_0(\beta,\alpha,\delta,\rho,q,A_{\min},A_{\max})$ with
--
--   $$\pi_{\Lambda^L,\beta,\rho}\bigl(\mathsf{Sorted}(\alpha,\delta)\bigr)\ \ge\ 1-\exp\bigl(-c_s(\alpha-1)\beta L\bigr)\qquad(\beta\ge\beta_0,\ L\ge L_0).$$
--
--   Here $\mathsf{Sorted}(\alpha,\delta)$ (Definition 1.1) asks for a comparison colouring $\tau$ of $D_L$, wired to $0$ on $B_L$, whose colour classes $R_i$ in $I_L$ each contain at most $\delta|R_i|$ sites where $\sigma$ differs from $i$, and whose energy is at most $\alpha H_*(L,\rho)$, the minimum energy at the prescribed counts.
--
--   This is the paper's main result: at low temperature a typical configuration with conserved colour counts is close to a colouring whose interfaces cost at most a factor $\alpha$ more than the cheapest possible arrangement, for arbitrary positive cost tables and arbitrary positive compositions.
--
--   **Formalization Note** The parameter dependences are encoded by quantifier order: $c_s$ is chosen from $(q,A_{\min},A_{\max},\rho_{\min})$ before $\rho$; $\beta_0$ after $\rho,\alpha,\delta$; $L_0$ after $\beta$; the cost matrix comes last, constrained only by its $A_{\min}$ and $A_{\max}$. Configurations are colourings of $I_L$ read on $D_L$ through the extension by $0$.
--
--   Differences from the source:
--   - reading: β0 = β0(α, δ, ρ, q, A_min, A_max), L0 = L0(β, α, δ, ρ, q, A_min, A_max) (Theorem 1), while Remark 1.2 and Appendix G write β0(q, A, ρ, α, δ) → β0 and L0 are chosen before the cost matrix and depend on it only through A_min and A_max; reason: the theorem's own printed dependence list, which is the stronger of the two readings; §§4–7 and Appendices A–C use A only through A_min, A_max
--   - encoding: c_s > 0 depends only on q, A_min, A_max and ρ_min → c_s is chosen after q, a = A_min, b = A_max, r = ρ_min and before every ρ with rhoMin ρ = r; reason: quantifier order expresses the dependence
--   - encoding: comparison colouring τ : D_L → {0, …, q−1} with τ|_{B_L} = 0 → τ a colouring of I_L read on D_L through its extension by 0; reason: the two descriptions are in bijection
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Theorem 1, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_IsDensity
import Definitions.Def_SpatialSorting_rhoMin
import Definitions.Def_SpatialSorting_sortedProb
open Classical Filter Topology

namespace SpatialSorting

/-- Theorem 1 — sorting at low temperature.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Theorem 1, p. 6 (PDF p. 7).

Formalization Notes:
- reading: β0 = β0(α, δ, ρ, q, A_min, A_max), L0 = L0(β, α, δ, ρ, q, A_min, A_max) (Theorem 1), while Remark 1.2 and Appendix G write β0(q, A, ρ, α, δ) → β0 and L0 are chosen before the cost matrix and depend on it only through A_min and A_max. The theorem's own printed dependence list, which is the stronger of the two readings; §§4–7 and Appendices A–C use A only through A_min, A_max.
- encoding: c_s > 0 depends only on q, A_min, A_max and ρ_min → c_s is chosen after q, a = A_min, b = A_max, r = ρ_min and before every ρ with rhoMin ρ = r. Quantifier order expresses the dependence.
- encoding: comparison colouring τ : D_L → {0, …, q−1} with τ|_{B_L} = 0 → τ a colouring of I_L read on D_L through its extension by 0. The two descriptions are in bijection. -/
theorem sorting_low_temperature :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ a b r : ℝ, 0 < a → a ≤ b → 0 < r →
      ∃ cs : ℝ, 0 < cs ∧
        ∀ ρ : Fin q → ℝ, IsDensity ρ → rhoMin ρ = r →
          ∀ α δ : ℝ, 1 < α → 0 < δ → δ < 1 →
            ∃ β0 : ℝ, ∀ β : ℝ, β0 ≤ β → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
              ∀ A : Matrix (Fin q) (Fin q) ℝ, IsCostMatrix A → amin A = a → amax A = b →
                1 - Real.exp (-(cs * (α - 1) * β * (L : ℝ))) ≤ sortedProb A β ρ L α δ := by sorry

end SpatialSorting
