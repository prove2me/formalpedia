-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_count_decomposition
-- name    : ScheduledQueue.Diffusion.count_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:56.201721+00:00
-- url     : https://prove2.me/theorems/61e5fa2a-9236-47a1-8f42-dc29ec5b3624
-- title:
--   Proof of Proposition 1, p. 4 — N(t) = #{ih + Uh ∈ (0, t]} + (𝓔(t) − 𝓛(t)) − (𝓔(0) − 𝓛(0))
-- statement:
--   Under the standing assumptions (i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), fix $t\ge 0$. Almost surely, the counts $\mathcal E(t),\mathcal L(t),\mathcal E(0),\mathcal L(0)$ are finite, only finitely many customers arrive in $(0,t]$, and
--   $$
--   N(t)=\Big(\sum_{ih+Uh\in(0,t]}1\Big)+\big(\mathcal E(t)-\mathcal L(t)\big)-\big(\mathcal E(0)-\mathcal L(0)\big).
--   $$
--
--   The identity splits the arrival count into the deterministic-rate count of scheduled slots and two stationary correction terms; it reduces the deviation $|N(s)-s/h|$ to the size of $\mathcal E$ and $\mathcal L$.
--
--   **Formalization Note** The page cites this identity from Proposition 2 of Araman et al. (2022). It is asserted almost surely at each fixed $t$, not simultaneously for all $t$: an arrival or a scheduled time exactly at $t$ or at $0$ breaks the identity, and that is a null event at each fixed time. The counts are compared as integers after the almost sure finiteness is established.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 4, proof of Proposition 1, display citing Proposition 2 of Araman et al. (2022)

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem count_decomposition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P,
      early h ξ U t ω ≠ ⊤ ∧ late h ξ U t ω ≠ ⊤ ∧
      early h ξ U 0 ω ≠ ⊤ ∧ late h ξ U 0 ω ≠ ⊤ ∧
      {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 t}.Finite ∧
      (ScheduledQueue.Stability.count h ξ U t ω : ℤ) =
        (scheduled h U t ω : ℤ)
          + (((early h ξ U t ω).toNat : ℤ) - ((late h ξ U t ω).toNat : ℤ))
          - (((early h ξ U 0 ω).toNat : ℤ) - ((late h ξ U 0 ω).toNat : ℤ)) := by sorry

end ScheduledQueue.Diffusion
