-- Prove2me | Theorems.Thm_PuhaWardFluid_Limit_theorem_1
-- name    : PuhaWardFluid.Limit.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:19.652159+00:00
-- url     : https://prove2.me/theorems/da0d170b-1386-4785-b402-dc51d983fb53
-- title:
--   Theorem 1, p. 17 — fluid-scaled states of admissible HL policies are tight; limit points are a.s. continuous fluid model solutions
-- statement:
--   Consider the sequence of multiclass $N$-server queues with reneging, each operated under an admissible head-of-the-line control policy, and suppose that Assumptions 4 and 5 hold, with arrival function limit $E$ and initial limit $(X^0,\nu^0,\eta^0)$. Then:
--
--   1. the fluid-scaled states $\{(\bar X^N,\bar\nu^N,\bar\eta^N)\}_{N\in\mathbb N}$ are tight in $\mathbf D(\mathbb X)$;
--   2. if $(X,\nu,\eta)$ is a distributional limit point of this sequence, then, almost surely, $(X,\nu,\eta)$ is a fluid model solution for $E$ with
--   $$(X(0),\nu(0),\eta(0))=(X^0,\nu^0,\eta^0);$$
--   3. almost surely, $(X,\nu,\eta)$ and the auxiliary functions $B,Q,R,D,K,I$ are continuous, and $\eta_j(t)$ does not charge points for all $t\ge0$ and classes $j$.
--
--   This is the fluid limit theorem of the paper: it holds for every sequence of admissible HL policies, idling and randomized ones included, and reduces the fluid limit of any specific policy to the characterization of fluid model solutions satisfying that policy's additional equations.
--
--   **Formalization Note** Tightness is stated as relative compactness in distribution (equivalent on the Polish space $\mathbf D(\mathbb X)$ by Prohorov's theorem). The limit point lives on its own probability space while $E$ and $(X^0,\nu^0,\eta^0)$ live on the space of the queues, so conclusions 2–3 are stated for a coupling: there is a probability space carrying $(\tilde E,\tilde X,\tilde\nu,\tilde\eta)$ such that $(\tilde X,\tilde\nu,\tilde\eta)$ has the law of the limit point, $(\tilde E,\tilde X(0),\tilde\nu(0),\tilde\eta(0))$ has the joint law of $(E,X^0,\nu^0,\eta^0)$, and almost surely $(\tilde X,\tilde\nu,\tilde\eta)$ is a fluid model solution for $\tilde E$ with the stated continuity and no-atom properties. This is what the proof (a joint limit with $\bar E^N$) delivers. Assumption 2 inside Assumption 5 is encoded as printed.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, p. 17 (PDF 18), Theorem 1

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Queue

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

/-- **Theorem 1** (Puha–Ward, p. 17). Under Assumptions 4 and 5, for any sequence of admissible HL
control policies, the fluid-scaled states `{(X̄^N, ν̄^N, η̄^N)}_N` are tight in `D(𝕏)`; every
distributional limit point `(X, ν, η)` is, almost surely, a fluid model solution for `E` with
`(X(0), ν(0), η(0)) = (X^0, ν^0, η^0)` (realized as a coupling `(E'', Y'')` in which `Y''` has the
law of the limit point and `(E'', Y''(0))` has the joint law of `(E, (X^0, ν^0, η^0))`); and,
almost surely, `(X, ν, η)` and the auxiliary functions are continuous and every `η_j(t)` does
not charge points. -/
theorem theorem_1 {J : ℕ} (hJ : 0 < J) (L : ClassLaws J) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : QueueSeq J Ω)
    (hQ : ∀ N : ℕ+, Q.IsAdmissibleHL L P N)
    (E : Ω → ℝ≥0 → Fin J → ℝ) (Z0 : Ω → Xsp L)
    (hA4 : Assumption4 L) (hA5 : Assumption5 L P Q E Z0) :
    RelCompactInDist (dX L) P (fun n => Q.fluidTriple L n.succPNat) ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (Y : Ω' → ℝ≥0 → Xsp L),
      IsDistLimitPoint (dX L) P (fun n => Q.fluidTriple L n.succPNat) P' Y →
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'')
        (E'' : Ω'' → ℝ≥0 → Fin J → ℝ) (Y'' : Ω'' → ℝ≥0 → Xsp L),
        IsProbabilityMeasure P'' ∧ IdentDistrib Y'' Y P'' P' ∧
        IdentDistrib (fun ω => (E'' ω, Y'' ω 0)) (fun ω => (E ω, Z0 ω)) P'' P ∧
        ∀ᵐ ω ∂P'', IsFluidSol L (E'' ω) (Y'' ω) ∧ Continuous (Y'' ω) ∧
          AuxContinuous L (Y'' ω) ∧ ∀ (t : ℝ≥0) (j : Fin J), NoCharge ((Y'' ω t).2.2 j) := by sorry

end PuhaWardFluid.Limit
