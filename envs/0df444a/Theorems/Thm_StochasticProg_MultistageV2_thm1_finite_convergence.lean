-- Prove2me | Theorems.Thm_StochasticProg_MultistageV2_thm1_finite_convergence
-- name    : StochasticProg.MultistageV2.thm1_finite_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:09:12.886461+00:00
-- url     : https://prove2.me/theorems/e681b4a4-a7c4-49ca-bfdf-401dda738bbf
-- title:
--   Finite convergence of the nested L-shaped method
-- statement:
--   **Theorem (Birge & Louveaux, Ch. 6, Thm. 1).** *If all $\Xi_t$ are finite and all $x_t$ have finite upper bounds, then the nested L-shaped method converges finitely to an optimal solution of (3.4.1).*
--
--   Formally: let a multistage stochastic linear program on a finite scenario tree be given such that for every stage $t$ and right-hand side $b$, the set $\{x\ge 0: W^tx=b\}$ is bounded above (all variables have finite upper bounds, written as rows of $W^t$), and every $W^t$ has linearly independent rows — an assumption added here, not in the book, so that the basic dual solutions of Step 1 exist. Then
--   1. there is no infinite sequence of iterations of the method (feasibility or optimality cuts, in any order) starting from the empty cut set of Step 0; and
--   2. in every cut set $C$ reachable from the empty one at which no further cut can be generated, either $\mathrm{NLDS}(1)$ is infeasible and (3.4.1) is infeasible, or $\mathrm{NLDS}(1)$ has an optimal solution, every optimal solution $(x^1,\theta^1)$ of $\mathrm{NLDS}(1)$ extends to a family $(x_k,\theta_k)_k$ in which each $(x_k,\theta_k)$ is optimal for $\mathrm{NLDS}(t,k)$ at $x_{a(k)}$, and every such family $(x_k)_k$ is feasible and optimal for (3.4.1), with $(c^1)^{\top}x^1+\theta^1$ equal to its expected cost (i.e. $\theta^1=\mathcal{Q}^2(x^1)$).
--
--   *Modelling choice:* a descendant's duals enter an optimality cut only after its Step 0 constraint $\theta=0$ has been replaced by optimality cuts, so that every cut is an outer linearisation, as the proof (p. 269) requires. This departs from the book's literal fast-forward-fast-back order: after an infeasibility that order can build a cut from duals that still carry $\theta=0$, and such a cut is invalid when future costs can be negative.
--
--   *Terminal* means that no cut can be generated at any current solution, which is stronger than the book's Step 2 stopping test ($t=2$ and no cut added to $\mathrm{NLDS}(1)$).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, Theorem 1, p. 268 (PDF p. 289), with Step 1 termination (p. 267) and the proof, p. 269 (PDF pp. 289–290)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_rhs
import Definitions.Def_StochasticProg_MultistageV2_Feasible
import Definitions.Def_StochasticProg_MultistageV2_obj
import Definitions.Def_StochasticProg_MultistageV2_Cuts
import Definitions.Def_StochasticProg_MultistageV2_Cuts_empty
import Definitions.Def_StochasticProg_MultistageV2_NLDSFeasible
import Definitions.Def_StochasticProg_MultistageV2_NLDSOptimal
import Definitions.Def_StochasticProg_MultistageV2_IsProposal
import Definitions.Def_StochasticProg_MultistageV2_IsInfeasibilityDualVertex
import Definitions.Def_StochasticProg_MultistageV2_feasCut
import Definitions.Def_StochasticProg_MultistageV2_IsOptimalDualVertex
import Definitions.Def_StochasticProg_MultistageV2_optCut
import Definitions.Def_StochasticProg_MultistageV2_Step

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- Birge & Louveaux, Chapter 6, Theorem 1 (p. 268): "If all `Ξ_t` are finite and all `x_t`
have finite upper bounds, then the nested L-shaped method converges finitely to an optimal
solution of (3.4.1)." Together with Step 1 ("If infeasible and `t = 1`, then stop; problem
(3.4.1) is infeasible", p. 267) and the proof (p. 269: the algorithm terminates either with
NLDS(1) infeasible or with `θ^1 = Q^2(x^1)`).

Formalized as follows. The state of the method is the cut set `C` of all subproblems
NLDS(t,k) (1.1)–(1.5); it starts from `Cuts.empty` (Step 0) and each iteration `Step` adds one
feasibility cut (Step 1) or one optimality cut (Step 2), in any order of visiting the
subproblems (p. 268: "Many alternative strategies are possible"). The theorem asserts:
1. *finite convergence*: there is no infinite run of `Step` from `Cuts.empty`;
2. *correct termination*: in every state reachable from `Cuts.empty` in which no further cut
   can be generated, either NLDS(1) is infeasible and (3.4.1) is infeasible, or NLDS(1) has an
   optimal solution, every optimal solution of NLDS(1) extends (by solving each NLDS(t,k) at its
   ancestor's current solution) to a full set of current solutions, and every such set of
   current solutions `xs` is feasible and optimal for (3.4.1), with
   `(c^1)ᵀ x^1 + θ^1` equal to its expected cost (`θ^1 = Q^2(x^1)`).

Hypotheses. "All `Ξ_t` finite": the scenario tree `T` has a `Fintype` of nodes. "All `x_t`
have finite upper bounds" (pp. 267–268): bounds are rows of the standard-form constraint
(1.2), so for each stage `t` and every right-hand side `b`, every `x ≥ 0` with `W^t x = b` is
bounded above by some `u` (`hbdd`). `W^t` has linearly independent rows (`hrank`):
an assumption ADDED here, not stated in the book. The "dual basic solutions" and "complementary
basic dual multipliers" of Step 1 (p. 267) are formalized as extreme points of the dual polyhedra
(`IsInfeasibilityDualVertex`, `IsOptimalDualVertex`); without full row rank those polyhedra may
contain a line and have no extreme point, so no optimality cut could ever be generated.
"Terminal" below means that no step applies at any current solution, which is stronger than the
book's Step 2 stopping test (t = 2 and no cut added to NLDS(1)).

Modelling choices. (a) A descendant's duals enter an optimality cut only after its Step-0
placeholder `θ = 0` has been replaced by optimality cuts (`Step.opt`, `hready`); with
`θ = 0` NLDS(k) is not a relaxation when future costs can be negative, and the proof's
induction (p. 269) uses exactly the outer-linearisation property. (b) Solutions and duals in
a step are those of the *current* subproblems. (c) Probabilities are unconditional; the
book's weights `p^t_k / p^{t-1}_j` appear in `optCut`. -/
theorem thm1_finite_convergence (inst : Instance H n m T)
    -- all `x_t` have finite upper bounds (pp. 267–268), bounds being rows of (1.2)
    (hbdd : ∀ (t : Fin H) (b : Fin m → ℝ), ∃ u : Fin n → ℝ, ∀ x : Fin n → ℝ,
      (∀ i, 0 ≤ x i) → (inst.W t).mulVec x = b → ∀ i, x i ≤ u i)
    -- standard form with full row rank: basic (dual) solutions exist (p. 267)
    (hrank : ∀ t : Fin H, LinearIndependent ℝ (fun r : Fin m => inst.W t r)) :
    (¬ ∃ s : ℕ → Cuts T n, s 0 = Cuts.empty T n ∧ ∀ i, Step inst (s i) (s (i + 1))) ∧
    ∀ C : Cuts T n, Relation.ReflTransGen (Step inst) (Cuts.empty T n) C →
      (∀ C' : Cuts T n, ¬ Step inst C C') →
      (((¬ ∃ x θ, NLDSFeasible inst C T.root 0 x θ) ∧ ¬ ∃ xs, Feasible inst xs) ∨
        ((∃ x θ, NLDSOptimal inst C T.root 0 x θ) ∧
          (∀ x θ, NLDSOptimal inst C T.root 0 x θ →
            ∃ (xs : T.Node → Fin n → ℝ) (θs : T.Node → ℝ), xs T.root = x ∧ θs T.root = θ ∧
              ∀ j, NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j)) ∧
          ∀ (xs : T.Node → Fin n → ℝ) (θs : T.Node → ℝ),
            (∀ j, NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j)) →
            Feasible inst xs ∧
            inst.c T.root ⬝ᵥ xs T.root + θs T.root = obj inst xs ∧
            ∀ xs', Feasible inst xs' → obj inst xs ≤ obj inst xs')) := by
  sorry

end StochasticProg.MultistageV2
