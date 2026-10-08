-- Prove2me | Theorems.Thm_SDDPConv_Doasa_theorem4
-- name    : SDDPConv.Doasa.theorem4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:44:05.26487+00:00
-- url     : https://prove2.me/theorems/79650b45-b37b-4140-9d12-c9903f36335f
-- title:
--   Theorem 4 — DOASA converges a.s. to an optimal policy in finitely many iterations (under the joint sampling property J)
-- statement:
--   Let a multistage stochastic linear program satisfy (A1)–(A4), with valid initial cuts $\theta_{t+1}\ge L_t$ and an LP oracle that returns optimal solutions of the approximate problems [AP$_t$] as a function of the cut set. Let the forward scenarios $\omega^k$ and backward samples $\Omega^k_t$ of DOASA satisfy the joint prefix sampling property **J**: for each stage $t=2,\dots,T$, each scenario $\omega(j)$ and each outcome $\omega_{ti}$, with probability 1 there are infinitely many iterations at which the forward scenario agrees with $\omega(j)$ in stages $2,\dots,t-1$ and $\omega_{ti}\in\Omega^k_t$.
--
--   Then with probability 1, for every DOASA run there is an iteration $K$ such that
--
--   1. the cut sets of all stages are constant from iteration $K$ on (so the forward solutions are those of a fixed policy $\bar x$);
--   2. the policy $\bar x$ induced by these cut sets is optimal: $\bar x_1$ solves [LP1] and, for every scenario and $2\le t\le T-1$, $\bar x_t$ solves [LP$_t(\bar x_{t-1},\omega_t)$];
--   3. the lower bound is exact:
--   $$C^K_1\;=\;Q_1 .$$
--
--   The paper states the theorem under FPSP and BPSP. These do not suffice: FPSP and BPSP constrain the forward and backward passes separately, while the proof needs each outcome's dual to be collected at the forward states of each scenario prefix. In a three-stage instance where the backward sample at the last stage is $\{c\}$ after forward outcome $a$ and $\{d\}$ after $b$, alternating, FPSP and BPSP hold but the cuts stabilize at a suboptimal policy with $C^k_1$ stuck below $Q_1$. We state the theorem under J, which implies both FPSP and BPSP and holds for every scheme the paper names (SDDP, AND, ReSa with $\Omega^k_t=\Omega_t$; CUPPS and independent forward and backward sampling by Borel–Cantelli).
--
--   This is the almost-sure finite convergence of SDDP-type algorithms, the standard justification for using them on multistage stochastic linear programs.
--
--   **Formalization Note** The conclusion holds for every run consistent with the samples, for every choice of extreme-point duals and of best-dual tie-breaks, inside `∀ᵐ`. Explicit readings (see the definitions): the trivial initial cut is replaced by a valid finite cut; (A4) is read on reachable states; the LP solver is a deterministic oracle on cut *sets*; collected duals are optimal extreme points; no cut is added while the dual collection is empty; probabilities sum to one. Lean iterations are numbered from $0$.
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), p. 12, Theorem 4 (corrected: J in place of FPSP and BPSP)

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model
import Definitions.Def_SDDPConv_Doasa_Cuts
import Definitions.Def_SDDPConv_Doasa_Run
import Definitions.Def_SDDPConv_Doasa_Sampling

open MeasureTheory

namespace SDDPConv.Doasa

/-- Theorem 4, p. 12, under the joint prefix sampling property J (which implies FPSP and BPSP;
FPSP and BPSP alone do not suffice): with probability 1, every DOASA run stops changing its cuts
after finitely many iterations, the policy induced by the final cuts is optimal for [LP1], and the
lower bound `C^K_1` equals the optimal value `Q_1`. -/
theorem theorem4 (I : Instance) (hA4 : A4 I) (L : ℕ → ℝ) (hL : ValidInit I L) (sol : Oracle I)
    (hsol : OracleSpec I L sol)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (fw : Ω' → ℕ → Scen I) (bw : Ω' → ℕ → (t : ℕ) → Finset (Fin (I.q t)))
    (hJ : JointSP I P fw bw) :
    ∀ᵐ w ∂P, ∀ (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t)),
      IsDOASARun I L sol (fw w) (bw w) cuts D →
        ∃ K, (∀ k, K ≤ k → ∀ t, cutset I cuts k t = cutset I cuts K t) ∧
          IsOptimalPolicy I (policy I sol (cutset I cuts K)) ∧
          apVal I 1 (cutset I cuts K 1) I.b₁ = Q₁ I := by sorry

end SDDPConv.Doasa
