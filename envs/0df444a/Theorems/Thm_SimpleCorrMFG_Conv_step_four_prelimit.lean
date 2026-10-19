-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_step_four_prelimit
-- name    : SimpleCorrMFG.Conv.step_four_prelimit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:17.361233+00:00
-- url     : https://prove2.me/theorems/2044b119-7154-4c82-a00a-023f2bdda8d8
-- title:
--   Proof of Theorem 6.1, Step Four, p. 24 — $P_N(X_1^N(t)\in\cdot\mid\mu^N(0),\dots,\mu^N(T))=\mu^N(t)(\cdot)$
-- statement:
--   Let $N\ge1$, let the initial states be i.i.d. with law $m\in\mathcal P(\mathcal X)$, let $\gamma^N$ be a symmetric correlated profile, assume $\Psi$ measurable and $f,F$ bounded measurable, and consider a realization of $(\otimes^N m,\gamma^N,\mathrm{Id})$. Let
--   $$\mu^N(t)=\frac1N\sum_{i=1}^N\delta_{X_i^N(t)},\qquad t\in\{0,\dots,T\},$$
--   be the empirical measure of all players. Then for every $t$,
--   $$P_N\big(X_1^N(t)\in\cdot\mid(\mu^N(0),\dots,\mu^N(T))\big)=\mu^N(t)(\cdot),$$
--   that is, for every $x\in\mathcal X$ and every Borel set $B\subseteq\mathcal P(\mathcal X)^{T+1}$,
--   $$P_N\big(X_1^N(t)=x,\ (\mu^N(0),\dots,\mu^N(T))\in B\big)=\mathbb E_N\big[\mathbf 1_B(\mu^N(0),\dots,\mu^N(T))\,\mu^N(t)(\{x\})\big].$$
--
--   This is the pre-limit form of the consistency condition; Lemma A.3 carries it to the limit.
--
--   **Formalization Note** The realization is the canonical one; player 1 is index `0`. As $\mathcal X$ is finite and $\mu^N(t)$ is a function of the flow, the displayed identity is equivalent to the conditional-law statement. The equilibrium property of $\gamma^N$ is not needed.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 24 (proof of Theorem 6.1, Step Four)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Proof of Theorem 6.1, Step Four (p. 24): for a symmetric profile and i.i.d. initial states, the
empirical flow `μ^N(t) = N⁻¹ ∑_{i=1}^N δ_{X_i(t)}` of all players satisfies
`P_N(X_1(t) ∈ · | μ^N(0), …, μ^N(T)) = μ^N(t)(·)`, stated as
`P_N(X_1(t) = x, μ^N(·) ∈ B) = E_N[1_B(μ^N(·)) μ^N(t)({x})]`. -/
theorem step_four_prelimit {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (m : Meas X)
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) (hγ : IsSymmetric γ)
    (t : Fin (T + 1)) (x : X) (B : Set (Flow T X)) (hB : MeasurableSet B) :
    (nLaw (prodInit N m) γ).real
        {ω | nPath M 0 id ω t 0 = x ∧ (fun s => empOn Finset.univ (nPath M 0 id ω s)) ∈ B} =
      ∫ ω, B.indicator (fun μ : Flow T X => ((μ t : Meas X) : X → ℝ) x)
        (fun s => empOn Finset.univ (nPath M 0 id ω s)) ∂(nLaw (prodInit N m) γ) := by sorry

end SimpleCorrMFG.Conv
