-- Prove2me | Theorems.Thm_TalagrandConc_SKModel_lipschitz
-- name    : TalagrandConc.SKModel.lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:25.943816+00:00
-- url     : https://prove2.me/theorems/58d0d107-cc7e-4567-b2b6-e9fa6ad0eef1
-- title:
--   Equation (12.6) — Lipschitz bound for log Z_N
-- statement:
--   Fix $N\ge1$ and $\beta>0$. For any two arrays of real couplings $h=(h_{ij})$ and $h'=(h'_{ij})$, let $F_N=\log Z_N$ be the logarithm of the partition function of (12.1). Then
--
--   $$|F_N(h)-F_N(h')|\le\frac{\beta}{\sqrt N}\sum_{1\le i<j\le N}|h_{ij}-h'_{ij}|.$$
--
--   This is the deterministic regularity bound used to transfer product-space concentration to the free energy.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 193, Eq. (12.6)

import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic

namespace TalagrandConc.SKModel

/-- Talagrand (12.6), p. 193. -/
theorem lipschitz (N : ℕ) (β : ℝ) (h h' : Interaction N → ℝ)
    (hN : 0 < N) (hβ : 0 < β) :
    |freeEnergy N β h - freeEnergy N β h'| ≤
      β / Real.sqrt N * ∑ p : Interaction N, |h p - h' p| := by sorry

end TalagrandConc.SKModel
