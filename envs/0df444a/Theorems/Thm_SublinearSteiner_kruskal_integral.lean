-- Prove2me | Theorems.Thm_SublinearSteiner_kruskal_integral
-- name    : SublinearSteiner.kruskal_integral
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:04.634274+00:00
-- url     : https://prove2.me/theorems/535f7c80-4ae1-4708-8616-e287a7972eef
-- title:
--   Kruskal integral (2.1): $L=\int_0^\infty(\kappa_T(a)-1)\,da$
-- statement:
--   For a nonempty terminal set $T$ with terminal MST weight $L$, and $\kappa_T(a)$ the number of components of the threshold graph $G_a(T)$,
--   $$L=\int_0^\infty\bigl(\kappa_T(a)-1\bigr)\,da.$$
--   This identity turns MST weight into a count of components across scales, which is what the scale-weighted statistics rely on.
--
--   **Formalization Note.** Integrability of the integrand is part of the conclusion.
--
--   Differences from the source:
--   - encoding: the integral for an instance → nonempty T, with integrability on (0, ∞) in the conclusion; reason: κ_T(a) − 1 is negative for empty T, where L is not meant; a Bochner integral needs integrability
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), (2.1), p.12

import Mathlib
import Definitions.Def_SublinearSteiner_ThresholdGraph

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), (2.1), p.12: Kruskal's algorithm gives `L = ∫₀^∞ (κ_T(a) − 1) da`.

**Formalization Note.** `T` is nonempty: `κ_T(a) − 1` is negative for empty `T`. The integrand vanishes above the largest
terminal distance, and it is a step function. Integrability is part of the conclusion, so the Bochner integral cannot
fall back on its junk value `0`. -/
theorem kruskal_integral {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (hT : T.Nonempty) (L : ℝ)
    (hL : IsTerminalMST T w L) :
    MeasureTheory.IntegrableOn (fun a : ℝ => (kappa w T a : ℝ) - 1) (Set.Ioi 0) ∧
      L = ∫ a in Set.Ioi (0 : ℝ), ((kappa w T a : ℝ) - 1) := by sorry

end SublinearSteiner
