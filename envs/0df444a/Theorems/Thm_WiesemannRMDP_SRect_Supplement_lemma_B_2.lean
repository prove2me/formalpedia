-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_Supplement_lemma_B_2
-- name    : WiesemannRMDP.SRect.Supplement.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:53:24.966911+00:00
-- url     : https://prove2.me/theorems/cc87b73c-da4d-4a93-85a7-26d0e6a434b6
-- title:
--   Lemma B.2 — under (A2) and (A3′) the state-action chain (45) satisfies Billingsley's conditions (C1)–(C4)
-- statement:
--   Let the structural model $\Xi_0$, $p^\xi(\cdot\mid s,a)=k_{sa}+K_{sa}\xi$ satisfy the standing assumptions (3) of the robust MDP model, and let $\pi_0$ be a stationary randomized policy. Consider the state-action chain (45): state set $\mathcal X=\{(s,a):\pi_0(a\mid s)>0\}$, parameter set $\Theta=\operatorname{int}\Xi_0$ and transition probabilities
--   $$p_{xy}(\theta)=p^\theta(s'\mid s,a)\,\pi_0(a'\mid s'),\qquad x=(s,a),\ y=(s',a')\in\mathcal X.$$
--   If the MDP satisfies (A2) (the chain $\widehat P(\pi_0;\xi)$ on $\mathcal S$ is irreducible for some $\xi\in\Xi_0$) and (A3′) (the rows $[K_{sa}]^\top_{s'\cdot}$ with $\pi_0(a\mid s)>0$ have full column rank $q$), then the chain satisfies the conditions of Theorem B.1:
--
--   1. (C1) every $\theta\mapsto p_{xy}(\theta)$ has continuous partial derivatives of third order throughout $\Theta$;
--   2. (C2) the set $D(\theta)=\{(x,y):p_{xy}(\theta)>0\}$ is the same for all $\theta\in\Theta$;
--   3. (C3) the Jacobian $\big(\partial p_{xy}(\theta)/\partial\theta_u\big)_{(x,y),u}$ has rank $q$ at every $\theta\in\Theta$;
--   4. (C4) for every $\theta\in\Theta$ the chain with transition probabilities $p_{xy}(\theta)$ is irreducible.
--
--   This is the step that lets the proof of Theorem 5.3 apply Billingsley's asymptotic theory of maximum likelihood for Markov chains (Theorem B.1, which the paper cites and does not prove).
--
--   **Formalization Note** (C1)–(C4) are `BillingsleyConditions`; $C^3$ is `ContDiffOn ℝ 3` and the Jacobian is built from Fréchet derivatives. The standing assumptions are the base model's `Model.Standing`, whose reward, discount and initial-law conjuncts do not occur in the statement.
--
--   Differences from the source:
--
--   - encoding: Theorem B.1 numbers the chain's states 1, …, X and writes U for the parameter dimension → the states are the subtype X of S × A and U = q; reason: (45a) and (45b) fix X and Θ ⊆ ℝ^q
--   - reading: "the MDP" of §5.1 satisfies definition (3) → the whole of `Model.Standing` is assumed, including r ≥ 0, λ ∈ (0, 1) and p₀ ∈ M(S); reason: §5.1 requires P0, Ξ0 to satisfy (3); the extra conjuncts concern r, λ, p₀, which do not occur in the statement, so no instance of the lemma is lost (any model can be given such r, λ, p₀)
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 47, Lemma B.2; (45) pp. 46–47; (C1)–(C4) of Theorem B.1, p. 46; (A2) p. 32; (A3') p. 34

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_WiesemannRMDP_SRect_Model
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Chains
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Inference

open MeasureTheory ProbabilityTheory Filter FoundationsML.ReinforcementLearning Matrix
open scoped Topology ENNReal

namespace WiesemannRMDP.SRect.Supplement

open WiesemannRMDP.SRect

/-- Lemma B.2 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*, Optimization Online
2610, revision of February 9, 2012, p. 47): if the MDP satisfies assumptions (A2) and (A3'), then
the Markov chain defined through (45) satisfies the conditions (C1)–(C4) of Theorem B.1.

The chain (45) has state set `X = {(s, a) : π0(a|s) > 0}`, parameter set `Θ = int Ξ0` and
transition probabilities `p_{xy}(θ) = p^θ(s'|s, a) π0(a'|s')`; (C1)–(C4) are
`BillingsleyConditions`.

**Formalization Note.** The structural model (§5.1, p. 29) is a `Model` satisfying the standing
assumptions (3) of §2.1 (`Model.Standing`); its reward and discount conjuncts play no role here.
The historical policy `π0` is a stationary randomized policy. -/
theorem lemma_B_2 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [DecidableEq Act] [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L)
    (hM : M.Standing) (π0 : St → Act → ℝ) (hπ0 : IsPolicy π0)
    (hA2 : A2 M π0) (hA3' : A3' M π0) :
    BillingsleyConditions M π0 := by sorry

end WiesemannRMDP.SRect.Supplement
