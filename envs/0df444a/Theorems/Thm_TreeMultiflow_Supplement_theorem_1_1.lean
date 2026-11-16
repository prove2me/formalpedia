-- Prove2me | Theorems.Thm_TreeMultiflow_Supplement_theorem_1_1
-- name    : TreeMultiflow.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:53:26.152923+00:00
-- url     : https://prove2.me/theorems/70a22bad-4e0e-453e-a090-cf7f55b7b697
-- title:
--   Theorem 1.1: every feasible LP solution rounds, in polynomial time, to a feasible request set keeping $4/11$ of its value
-- statement:
--   Let $T$ be a tree with integer edge capacities $u_e\ge 1$, and let $F$ be a finite collection of labeled requests, request $f$ having endpoints $s_f,t_f$ (possibly equal), a nonnegative weight $w_f$, and the unique tree path $\mathrm{Path}(f)$ between its endpoints. A **feasible solution of (1)** is a vector $x\in\mathbb R^F$ with $0\le x_f\le 1$ and $\sum_{f:\,e\in\mathrm{Path}(f)}x_f\le u_e$ for every edge $e$; a set $S\subseteq F$ is **feasible** when at most $u_e$ of its requests use each edge $e$. The theorem asserts:
--
--   1. For every feasible solution $x$ of (1) there is a feasible subset $S\subseteq F$ with
--   $$
--   w(S)=\sum_{f\in S}w_f \;\ge\; \frac{4}{11}\sum_{f\in F}w_f x_f .
--   $$
--   2. For rationally encoded inputs, such a subset can be found in polynomial time: some algorithm, running in time polynomial in the length of the binary encoding of the tree, the capacities, the requests, the weights and $x$, outputs such a set $S$.
--
--   This is the first stage of the paper's argument (the $11/4$ bound); Theorem 1.2 improves the constant to $2/5$ by saving one of the eleven colours. Theorem 1.1 prints no integrality-gap clause and none is stated here.
--
--   **Formalization Note** The two clauses have exactly the shape of clauses (A) and (C) of the published goal `TreeMultiflow.theorem_1_2`, with $2/5$ replaced by $4/11$. The vertex type is arbitrary (finitely many requests use finitely many edges). Polynomial time is `Turing.TM2ComputableInPolyTime` for the published binary encoding `encRatInstance` over the alphabet `OnlineCRS.Combine.Sym`; the algorithm's output is a Boolean mask over the requests (read with default `false`), and correctness is required on every well-formed rational instance whose $x$ is a feasible solution of (1).
--
--   Differences from the source:
--   - encoding: a tree with capacities, requests and weights → SimpleGraph V with IsTree and no Fintype V; capacities Sym2 V → ℕ with 1 ≤ u e on G.edgeSet; a Fintype index type F with endpoint maps src, dst; real weights w ≥ 0; reason: same instances (finitely many requests use finitely many edges)
--   - encoding: rationally encoded inputs, polynomial time → Turing.TM2ComputableInPolyTime for encRatInstance (binary numbers, alphabet OnlineCRS.Combine.Sym), output a request mask read with getD … false, correctness on WellFormed instances with IsLPFeasible lpval; reason: the base mission's fixed machine model and encoding, the same as Theorem 1.2 (C)
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 1.1, p.3 (LP (1), p.2; algorithmic claim, p.8)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_TreeMultiflow_IsFeasible
import Definitions.Def_TreeMultiflow_IsLPFeasible
import Definitions.Def_TreeMultiflow_RatInstance
import Definitions.Def_TreeMultiflow_RatInstance_graph
import Definitions.Def_TreeMultiflow_RatInstance_cap
import Definitions.Def_TreeMultiflow_RatInstance_src
import Definitions.Def_TreeMultiflow_RatInstance_dst
import Definitions.Def_TreeMultiflow_RatInstance_weight
import Definitions.Def_TreeMultiflow_RatInstance_lpval
import Definitions.Def_TreeMultiflow_RatInstance_WellFormed
import Definitions.Def_TreeMultiflow_encRatInstance

universe u₁ u₂

namespace TreeMultiflow.Supplement

/-- **Theorem 1.1: 4/11 rounding, in polynomial time.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 1.1,
p.3: "For every feasible solution x of (1), there is a feasible subset S ⊆ F of requests such that
w(S) ≥ (4/11) Σ_{f∈F} w_f x_f. Moreover, for rationally encoded inputs, such a subset can be found
in polynomial time."
Setting (p.2): a tree with integer capacities uₑ ≥ 1, a finite collection of labeled requests with
nonnegative weights, each with the unique tree path between its endpoints.

The two clauses:

* **(A)** for every tree `G` with capacities `u ≥ 1` on its edges, labeled requests `F` with
  endpoints `src`, `dst`, weights `w ≥ 0`, and every feasible solution `x` of (1), some feasible
  `S` has `Σ_{f∈S} w f ≥ (4/11) Σ_f w f x f`;
* **(C)** some map `alg`, computable by a Turing machine in time polynomial in the length of the
  binary encoding `encRatInstance`, returns on every well-formed rational instance with a
  feasible `x` a mask of a set `S` with the property of (A).

Theorem 1.1 prints no integrality-gap clause; none is stated.

**Formalization Note.** Shaped exactly as clauses (A) and (C) of `TreeMultiflow.theorem_1_2`
with `2/5` replaced by `4/11`. The vertex type is arbitrary (no `Fintype V`); finitely many
requests use only finitely many edges, and the finite case is the paper's. Polynomial time is
`Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym` with binary numbers;
the fractional solution is part of the input; the output mask is read with `getD … false`. -/
theorem theorem_1_1 :
    (∀ (V : Type u₁) (F : Type u₂) [Fintype F] (G : SimpleGraph V), G.IsTree →
      ∀ u : Sym2 V → ℕ, (∀ e ∈ G.edgeSet, 1 ≤ u e) →
      ∀ (src dst : F → V) (w : F → ℝ), (∀ f, 0 ≤ w f) →
      ∀ x : F → ℝ, IsLPFeasible G u src dst x →
        ∃ S : Finset F, IsFeasible G u src dst S ∧
          (4 / 11 : ℝ) * ∑ f, w f * x f ≤ ∑ f ∈ S, w f) ∧
    (∃ alg : RatInstance → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encRatInstance (fun m : List Bool => m) alg) ∧
      ∀ I : RatInstance, I.WellFormed → IsLPFeasible I.graph I.cap I.src I.dst I.lpval →
        IsFeasible I.graph I.cap I.src I.dst
            (Finset.univ.filter fun f : Fin I.reqs.length => (alg I).getD f false = true) ∧
          (4 / 11 : ℝ) * ∑ f, I.weight f * I.lpval f ≤
            ∑ f ∈ Finset.univ.filter (fun f : Fin I.reqs.length => (alg I).getD f false = true),
              I.weight f) := by sorry

end TreeMultiflow.Supplement
