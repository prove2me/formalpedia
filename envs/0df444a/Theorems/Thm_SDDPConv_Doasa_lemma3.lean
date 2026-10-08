-- Prove2me | Theorems.Thm_SDDPConv_Doasa_lemma3
-- name    : SDDPConv.Doasa.lemma3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:44:03.258076+00:00
-- url     : https://prove2.me/theorems/990027e9-4bcf-4d29-8393-f1f601e2207a
-- title:
--   Lemma 3 — DOASA-N over all scenarios converges a.s. to an optimal policy (BPSP per scenario)
-- statement:
--   Fix an instance satisfying (A4), valid initial cuts and an LP oracle meeting its specification. Run DOASA-N with a scenario list containing **every** scenario (the "universe of scenarios"), with backward samples $\Omega^k_{s,t}$ satisfying BPSP for each scenario $s$: for each $s$, $t$ and $i$, with probability 1, $\omega_{ti}\in\Omega^k_{s,t}$ for infinitely many $k$. Then with probability 1, for every run there is an iteration $K$ such that
--
--   1. the cut sets of all stages are constant from $K$ on;
--   2. the policy $(\bar x_1,\bar x_2(\omega_2),\bar x_3(\omega_2,\omega_3),\dots)$ induced by the cut sets of iteration $K$ is optimal: $\bar x_1$ solves [LP1] and, for every scenario and $2\le t\le T-1$, $\bar x_t$ solves [LP$_t(\bar x_{t-1},\omega_t)$];
--   3. the lower bound is exact: $C^K_1=Q_1$.
--
--   The paper states the lemma under BPSP, with the samples $\Omega^k_{s,t}$ of DOASA-N. We read BPSP per scenario. The weaker reading, "$\omega_{ti}\in\Omega^k_{s,t}$ for some $s$ infinitely often", does not suffice: a stage-$t$ cut becomes exact at a state only when the outcome's dual is collected at that state, and a two-scenario counterexample (outcome collected only along the other scenario) leaves the limiting policy suboptimal.
--
--   **Formalization Note** The conclusion holds for every run consistent with the samples (every choice of extreme-point duals and tie-breaks), inside the almost-sure quantifier. The scenario list may contain repetitions. The paper's trivial initial cut is replaced by valid finite cuts, and the LP solver is modelled as a deterministic oracle on cut sets (see the definitions).
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), p. 10, Lemma 3 (proof pp. 10–11)

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model
import Definitions.Def_SDDPConv_Doasa_Cuts
import Definitions.Def_SDDPConv_Doasa_Run
import Definitions.Def_SDDPConv_Doasa_Sampling

open MeasureTheory

namespace SDDPConv.Doasa

/-- Lemma 3, p. 10 (BPSP read per scenario): DOASA-N whose scenario list contains every scenario
converges with probability 1, after finitely many iterations, to an optimal policy of [LP1], and
the lower bound `C^K_1` equals `Q_1`. -/
theorem lemma3 (I : Instance) (hA4 : A4 I) (L : ℕ → ℝ) (hL : ValidInit I L) (sol : Oracle I)
    (hsol : OracleSpec I L sol) (Ls : List (Scen I)) (hLs : ∀ sc : Scen I, sc ∈ Ls)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (bw : Ω' → ℕ → Scen I → (t : ℕ) → Finset (Fin (I.q t))) (hbw : BPSPN I P bw) :
    ∀ᵐ w ∂P, ∀ (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t)),
      IsDOASANRun I L sol Ls (bw w) cuts D →
        ∃ K, (∀ k, K ≤ k → ∀ t, cutset I cuts k t = cutset I cuts K t) ∧
          IsOptimalPolicy I (policy I sol (cutset I cuts K)) ∧
          apVal I 1 (cutset I cuts K 1) I.b₁ = Q₁ I := by sorry

end SDDPConv.Doasa
