-- Prove2me | Theorems.Thm_PalmQueueing_Palm_wald_generalization
-- name    : PalmQueueing.Palm.wald_generalization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T21:15:04.708329+00:00
-- url     : https://prove2.me/theorems/5f83b0d6-71fe-40ff-9dbc-5de04f0be066
-- title:
--   Eq. (1.3.8) — the exchange formula as a generalization of Wald's identity
-- statement:
--   **Remark 1.3.3.** Formula (1.3.6) can also be viewed as a generalization of *Wald's
--   identity*, since it reads
--   $$ E^0_{N'}\Big[ \sum_{k=1}^{N((0, T'_1])} f \circ \theta_{T_k} \Big]
--   \;=\; E^0_{N'}\big[ N((0, T'_1]) \big]\; E^0_N[f] . \tag{1.3.8} $$
--
--   The expectation of a sum with a random number of summands factors into the expectation of the
--   number of summands times the (Palm) expectation of one summand — without any independence
--   hypothesis between the two, which is the sense in which it generalizes Wald.
--
--   The sum $\sum_{k=1}^{N((0,T'_1])}$ is the sum over those $k \in \mathbb{Z}$ with
--   $T_k \in (0, T'_1]$: under the convention $T_0 \le 0 < T_1$, $T_k > 0$ holds exactly for
--   $k \ge 1$.
--
--   The ergodic-limit argument (1.3.7) that the book gives on the same page for the underlying formula
--   is explicitly labelled heuristic — "Such a proof is only heuristic in particular because one has to
--   justify the second equality" — and is deliberately not stated as a result.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 23, Remark 1.3.3, Eq. (1.3.8)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.3.8): the exchange formula as a generalization of Wald's identity (Remark 1.3.3, p.23)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Eq. (1.3.8)** (Remark 1.3.3, p.23): the exchange formula, read as a **generalization of
Wald's identity**,

`E⁰_{N'} [ Σ_{k=1}^{N((0,T'₁])} f ∘ θ_{T_k} ] = E⁰_{N'} [ N((0,T'₁]) ] · E⁰_N[f]`.

The random number of summands and the summands are not assumed independent — that is the sense in
which it generalizes Wald. The sum `Σ_{k=1}^{N((0,T'₁])}` is written here as the sum over all
`k ∈ ℤ` of the terms with `T_k ∈ (0, T'₁]`, which is the same sum because `T_k > 0` exactly for
`k ≥ 1` under the convention `T₀ ≤ 0 < T₁`.

The ergodic-limit argument `(1.3.7)` that the book gives on the same page for the underlying
formula is explicitly labelled heuristic ("Such a proof is only heuristic") and is not stated
here. -/
theorem wald_generalization (S S' : PalmSetting Ω)
    (hflow : S'.θ = S.θ) (hprob : S'.P = S.P)
    (f : Ω → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, ∑' k : ℤ,
        Set.indicator (Set.Ioc (0 : ℝ) (S'.N.T 1 ω))
          (fun _ => f (S.θ (S.N.T k ω) ω)) (S.N.T k ω) ∂S'.P0
      = (∫⁻ ω, S.N.count ω (Set.Ioc (0 : ℝ) (S'.N.T 1 ω)) ∂S'.P0) * ∫⁻ ω, f ω ∂S.P0 := by sorry

end PalmQueueing.Palm
