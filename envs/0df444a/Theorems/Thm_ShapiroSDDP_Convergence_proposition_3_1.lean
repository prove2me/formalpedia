-- Prove2me | Theorems.Thm_ShapiroSDDP_Convergence_proposition_3_1
-- name    : ShapiroSDDP.Convergence.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:23.299004+00:00
-- url     : https://prove2.me/theorems/b65c1046-57bf-4661-925b-d074b34e17b0
-- title:
--   Proposition 3.1 — with subsampling, (A1) and basic optimal solutions, SDDP yields an optimal SAA policy after finitely many iterations w.p.1
-- statement:
--   Consider the SAA of a multistage linear stochastic program with $T\ge2$ stages whose cost-to-go functions are finite valued on reachable decisions. Run the SDDP method from valid initial cut sets $C_0$, with a deterministic LP oracle that returns an optimal solution of (3.13), resp. (3.14), whenever one exists, and with $M\ge1$ forward scenarios per iteration drawn by the subsampling procedure (mutually independent, uniform on the SAA scenarios). Then, with probability one, the following holds for every run of the method on the drawn scenarios (every choice of basic optimal dual solutions in the backward steps) along which assumption (A1) holds: there is an iteration $K$ such that for all $k\ge K$ the forward step policy
--   $$\bar x_1\in\arg\min\{c_1^\top x_1+\mathfrak Q^k_2(x_1):A_1x_1=b_1,x_1\ge0\},\qquad \bar x_t\in\arg\min\{\tilde c_t^\top x_t+\mathfrak Q^k_{t+1}(x_t):\tilde A_tx_t=\tilde b_t-\tilde B_t\bar x_{t-1},x_t\ge0\}$$
--   defined by the iteration-$k$ approximations $\mathfrak Q^k_{t+1}$ is an optimal policy for the SAA problem.
--
--   This is the finite convergence result of the paper for SDDP applied to the SAA problem: the lower approximations stop changing, and the policy they define attains the SAA optimal value.
--
--   **Formalization Note** The paper states the result under "the subsampling procedure is used, assumption (A1) holds and in the backward steps the basic optimal solutions are employed"; we state it with the following explicit readings. Cost-to-go functions are finite valued on reachable decisions (the paper: everywhere). The initial cut sets are an explicit parameter, nonempty and valid (the paper leaves them unspecified). The forward solutions come from a deterministic oracle on cut sets, and the result holds for every such oracle. Basic optimal duals are an arbitrary existential choice, and the result holds for every run. (A1) is a hypothesis on the run. There are $M\ge1$ forward scenarios per iteration, drawn i.i.d. uniformly. Within an iteration the forward step precedes the backward step, which builds cuts at that iteration's forward trial points. "After a sufficiently large number of backward and forward steps" is read as "for every iteration from some $K$ on". Optimality is minimal expected cost among feasible implementable policies.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, p. 10, Proposition 3.1

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model
import Definitions.Def_ShapiroSDDP_Convergence_SDDP
import Definitions.Def_ShapiroSDDP_Convergence_Sampling

open MeasureTheory

namespace ShapiroSDDP.Convergence

/-- Proposition 3.1, p. 10: if the forward steps use the subsampling procedure (`M ≥ 1` i.i.d.
uniform scenarios of the SAA problem per iteration), assumption (A1) holds and the backward steps
use basic optimal dual solutions, then with probability one, from some iteration on, the forward
step procedure (3.13)–(3.14) defines an optimal policy for the SAA problem. -/
theorem proposition_3_1 (I : Instance) (hfin : FiniteValued I) (C₀ : (t : ℕ) → Finset (Cut I t))
    (hC₀ : ValidInit I C₀) (sol : Oracle I) (hsol : OracleSpec I sol) {M : ℕ} (hM : 0 < M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Fin M → Ω → Scen I) (hX : IsUniformIID I P X) :
    ∀ᵐ w ∂P, ∀ cuts : ℕ → (t : ℕ) → Finset (Cut I t),
      IsRun I C₀ sol (fun k i => X k i w) cuts → A1 I sol cuts →
        ∃ K, ∀ k, K ≤ k → IsOptimalPolicy I (fwd I sol (cuts k)) := by sorry

end ShapiroSDDP.Convergence
