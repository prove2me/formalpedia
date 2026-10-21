-- Prove2me | Theorems.Thm_PuhaWardFluid_Limit_lemma_2_i
-- name    : PuhaWardFluid.Limit.lemma_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:28.381202+00:00
-- url     : https://prove2.me/theorems/2a153ae7-af71-4650-809d-d84d29456866
-- title:
--   Lemma 2 (i), p. 15 — continuous E and K make a fluid model solution and its auxiliary functions continuous
-- statement:
--   Let $E$ be an arrival function and $(X,\nu,\eta)$ a fluid model solution for $E$. If $E$ and the auxiliary function $K$ are continuous, then $(X,\nu,\eta)$, as a path in $\mathbb X$ with the product of the Euclidean and weak topologies, is continuous, and so are the auxiliary functions $B$, $Q$, $R$, $D$, $K$ (every coordinate) and $I$:
--   $$E,\ K\ \text{continuous}\ \Longrightarrow\ (X,\nu,\eta),\ B,\ Q,\ R,\ D,\ K,\ I\ \text{continuous}.$$
--
--   In the proof of Theorem 1 this lemma upgrades the continuity of the limits of $\bar E^N$ and $\bar K^N$ to continuity of the whole fluid limit.
--
--   **Formalization Note** Parts (ii) and (iv) of Lemma 2 (absolute continuity) are not posed.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, p. 15 (PDF 16), Lemma 2 (i)

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_FluidModel

open MeasureTheory
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

/-- **Lemma 2 (i)** (p. 15). If `(X, ν, η)` is a fluid model solution for the arrival function `E`,
and `E` and the auxiliary function `K` are continuous, then `(X, ν, η)` and each of the auxiliary
functions are continuous. -/
theorem lemma_2_i {J : ℕ} (L : ClassLaws J) (E : ℝ≥0 → Fin J → ℝ) (y : ℝ≥0 → Xsp L)
    (hsol : IsFluidSol L E y) (hE : Continuous E)
    (hK : ∀ j, Continuous fun t => flK L y t j) :
    Continuous y ∧ AuxContinuous L y := by sorry

end PuhaWardFluid.Limit
