-- Prove2me | Theorems.Thm_ProcessingNetworks_LyapunovCriteria_regular_point_zero_buffer_zero_drift
-- name    : ProcessingNetworks.LyapunovCriteria.regular_point_zero_buffer_zero_drift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:59:14.641712+00:00
-- url     : https://prove2.me/theorems/e736d1f1-765f-4a29-a3c8-7e434f9b5558
-- title:
--   Lemma 8.9 — zero buffer content implies zero drift at a regular point (milestone)
-- statement:
--   **Lemma 8.9.** Assume $t > 0$ is a regular point of a fluid model solution $(D,F,T,Z)$. Then
--   $Z_i(t) = 0$ implies $\dot Z_i(t) = 0$.
--
--   This is the "corrected version of (7.22)" mission IV's Theorem 7.8 promised (Remark 7.9): at
--   a regular point where a buffer is empty, the fluid arrival and departure rates into that
--   buffer necessarily coincide (both equal $\dot Z_i(t) = 0$), even though the *service* rate
--   itself need not be zero there. It is the key technical tool making the "buffer empty" case of
--   a drift-condition verification tractable (see Theorem 8.12's proof, which invokes it
--   directly), since $Z_i \equiv 0$ is not assumed identically — only that it happens to vanish at
--   the single regular point $t$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 138, Lemma 8.9

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_RegularPoint

namespace ProcessingNetworks.LyapunovCriteria

/-- Lemma 8.9, Dai & Harrison p. 138 (PDF p. 154): assume `t > 0` is a regular point of a fluid
model solution `(D,F,T,Z)`. Then `Zᵢ(t) = 0` implies `Żᵢ(t) = 0`. -/
theorem regular_point_zero_buffer_zero_drift
    {I J K : ℕ} (dat : FluidEquationData I J K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat Dh Fh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Dh Fh Th Zh t)
    (i : Fin I) (hz : Zh t i = 0) :
    HasDerivAt (fun s => Zh s i) 0 t := by sorry

end ProcessingNetworks.LyapunovCriteria
