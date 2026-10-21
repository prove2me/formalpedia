-- Prove2me | Theorems.Thm_PuhaWardFluid_Limit_lemma_2_iii
-- name    : PuhaWardFluid.Limit.lemma_2_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:22.947281+00:00
-- url     : https://prove2.me/theorems/7457e952-7798-4e5b-bd16-c046242284b8
-- title:
--   Lemma 2 (iii), p. 15 — atomless initial measures stay atomless along a fluid model solution
-- statement:
--   Let $E$ be an arrival function and $(X,\nu,\eta)$ a fluid model solution for $E$.
--
--   1. If $K$ is continuous and $\nu_j(0)$ has no atoms for every class $j$, then $\nu_j(t)$ has no atoms for every $t\ge0$ and $j$.
--   2. If $E$ is continuous and $\eta_j(0)$ has no atoms for every class $j$, then $\eta_j(t)$ has no atoms for every $t\ge0$ and $j$.
--
--   A measure has no atoms (does not charge points) if it gives zero mass to every singleton $\{x\}$. Together with Assumption 5.2, part 2 yields the "does not charge points" conclusion of Theorem 1, which in turn is needed to identify the limiting reneging process.
--
--   **Formalization Note** "$K$ is continuous" is stated coordinatewise. Parts (ii) and (iv) of Lemma 2 are not posed.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, p. 15 (PDF 16), Lemma 2 (iii)

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_FluidModel

open MeasureTheory
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

/-- **Lemma 2 (iii)** (p. 15). Let `(X, ν, η)` be a fluid model solution for the arrival function
`E`. If `K` is continuous and every `ν_j(0)` has no atoms, then every `ν_j(t)` has no atoms; if `E`
is continuous and every `η_j(0)` has no atoms, then every `η_j(t)` has no atoms. -/
theorem lemma_2_iii {J : ℕ} (L : ClassLaws J) (E : ℝ≥0 → Fin J → ℝ) (y : ℝ≥0 → Xsp L)
    (hsol : IsFluidSol L E y) :
    ((∀ j, Continuous fun t => flK L y t j) → (∀ j, NoCharge (flNu L y 0 j)) →
        ∀ (t : ℝ≥0) j, NoCharge (flNu L y t j)) ∧
    (Continuous E → (∀ j, NoCharge (flEta L y 0 j)) →
        ∀ (t : ℝ≥0) j, NoCharge (flEta L y t j)) := by sorry

end PuhaWardFluid.Limit
