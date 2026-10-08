-- Prove2me | Theorems.Thm_PalmQueueing_Formulas_palm_workload_gap
-- name    : PalmQueueing.Formulas.palm_workload_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:31:09.743014+00:00
-- url     : https://prove2.me/theorems/1d13105d-f5b5-4e26-bda9-391ca0b3aba6
-- title:
--   Lemma 3.5.2 — the gap between the two Palm expectations of the workload
-- statement:
--   **Lemma 3.5.2.** With the assumptions and the notation of Property 3.5.1,
--   $$ E^0_{N^i}[W(0)] = E^0_{A^i}[W(0)] - \frac{C_i}{\alpha_i} . \tag{3.5.32} $$
--
--   Two Palm expectations of the same workload, taken with respect to two different point processes of
--   the same source: $N^i$, whose points are the instants source $i$ switches **on**, and $A^i$, whose
--   points are weighted by the **fluid** it brings. They differ by exactly $C_i/\alpha_i$, with
--   $C_i = \lambda_i E^0_{N^i}[\int_0^{X^i_0}(A_{0,t} - ct)A^i(dt)]$ the fluid-weighted excess of
--   arrivals over service accumulated during source $i$'s on period.
--
--   Read the other way: a unit of fluid from source $i$ arrives, on average, into a buffer that is
--   $C_i/\alpha_i$ fuller than the buffer the source finds when it wakes up, because the source's own
--   earlier fluid is still there.
--
--   The proof is the Neveu exchange formula — in the extension of Exercise 1.3.1 to a general
--   $\theta_t$-compatible random measure — applied to $N^i$ and $A^i$:
--   $$ \alpha_i E^0_{A^i}[W(0)] = \lambda_i E^0_{N^i}\Big[\int_0^{T^i_1} W(t)A^i(dt)\Big] , $$
--   after which $W(t) = W(0) + A_{0,t} - ct$ on the on period and the independence assumptions give
--   the result.
--
--   Together with Lemma 3.5.1 the pair reduces Property 3.5.1's formula (3.5.26) to two applications
--   of the exchange formula.
--
--   **Formalization Note.** The page's identity is between finite quantities; the statement assumes
--   that $E^0_{A^i}[W(0)]$ and the expectation defining $C_i$ are finite, so that no Bochner integral
--   takes the value $0$ by convention.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 247, Lemma 3.5.2

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Formulas_OnOffSources

/-!
# Lemma 3.5.2: the gap between the two Palm expectations of the workload (§3.5.3, p.247)
-/

namespace PalmQueueing.Formulas

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 3.5.2** (p.247). With the assumptions and the notation of Property 3.5.1,

`(3.5.32)  E⁰_{N^i}[W(0)] = E⁰_{A^i}[W(0)] − C_i / α_i`.

Two Palm expectations of the same workload, taken with respect to two different point processes of
the same source: `N^i`, whose points are the instants source `i` switches **on**, and `A^i`, whose
points are weighted by the **fluid** it brings. They differ by exactly `C_i/α_i`, where

`(3.5.27)  C_i = λ_i E⁰_{N^i}[ ∫_0^{X^i_0} (A_{0,t} − ct) A^i(dt) ]`

is the fluid-weighted excess of arrivals over service accumulated during source `i`'s on period.

Read the other way: a unit of fluid from source `i` arrives, on average, into a buffer that is
`C_i/α_i` fuller than the buffer the source finds when it wakes up — because the source's own
earlier fluid is still there. Together with Lemma 3.5.1 the pair reduces Property 3.5.1's formula
`(3.5.26)  E[W(0)] = Σ_i (C_i − α_i D_i)/(c − α)` to two applications of the exchange formula.

The proof is the Neveu exchange formula, in the extension of Exercise 1.3.1 to a general
`θ_t`-compatible random measure, applied to `N^i` and `A^i`:
`α_i E⁰_{A^i}[W(0)] = λ_i E⁰_{N^i}[∫_0^{T^i_1} W(t) A^i(dt)]`, after which
`W(t) = W(0) + A_{0,t} − ct` on the on period and the independence assumptions give the result.

The page's identity is between finite quantities; `hWA` and `hC` say that `E⁰_{A^i}[W(0)]` and the
expectation defining `C_i` are finite, so that neither Bochner integral takes the junk value `0`. -/
theorem palm_workload_gap {k : ℕ} (M : OnOffModel Ω k) (i : Fin k)
    (nu : Fin k → ℝ) (hprop : M.Property351 nu)
    (hWA : Integrable (fun ω => M.W 0 ω) (M.P0A i))
    (hC : Integrable (fun ω => M.Cintegrand i ω) (M.P0N i)) :
    ∫ ω, M.W 0 ω ∂(M.P0N i)
      = (∫ ω, M.W 0 ω ∂(M.P0A i)) - M.Cconst i / M.alphaI i := by sorry

end PalmQueueing.Formulas
