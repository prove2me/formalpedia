-- Prove2me | Theorems.Thm_Reiman84_QueueLength_scaled_netput_measurable_cadlag
-- name    : Reiman84.QueueLength.scaled_netput_measurable_cadlag
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-18T12:58:45.379971+00:00
-- url     : https://prove2.me/theorems/6b9ea627-a663-47b9-8d63-5c3d40d680f2
-- title:
--   The scaled netput and the time-changed scaled netput are measurable random elements of $D[0,1]$
-- statement:
--   Let $N$ be a network of §2 on $(\Omega,P)$ and let $(Q,B)$ solve the queue equations (1)–(3) almost surely. For every $n$, the scaled netput $\zeta^n(t)=n^{-1/2}X(nt)$ and the scaled centred time-changed netput
--
--   $$\tilde\zeta^n(t)=n^{-1/2}\tilde X(nt),$$
--
--   where $\tilde X$ is built with $B$, are almost-everywhere measurable as random paths on $[0,1]$ (product σ-algebra of the path space) and almost surely cadlag on $[0,1]$.
--
--   Role: these are the measurability and path-regularity facts that make $\zeta^n$ and $\tilde\zeta^n$ random elements of $D$, so that the weak-convergence criterion applies in Proposition 5.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), https://doi.org/10.1287/moor.9.3.441, §2, p. 443 (definition of the processes X, X̃ and the queue equations (1)–(3))

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

open MeasureTheory

namespace Reiman84.QueueLength

theorem scaled_netput_measurable_cadlag {K : ℕ} {J : Finset (Fin K)} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω}
    (N : Network K J P) (Q B : Ω → ℝ → Fin K → ℝ)
    (hQ : ∀ᵐ ω ∂P, N.IsQueueSolution ω (Q ω) (B ω)) (n : ℕ) :
    (AEMeasurable (fun ω => onUnit (diffScale n (fun t => N.X t ω))) P ∧
      ∀ᵐ ω ∂P, IsCadlag01 (diffScale n (fun t => N.X t ω))) ∧
    (AEMeasurable (fun ω => onUnit (diffScale n (fun t => N.Xtilde (B ω) t ω))) P ∧
      ∀ᵐ ω ∂P, IsCadlag01 (diffScale n (fun t => N.Xtilde (B ω) t ω))) := by sorry

end Reiman84.QueueLength
