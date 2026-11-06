-- Prove2me | Theorems.Thm_TreeMultiflow_theorem_2_1_polytime
-- name    : TreeMultiflow.theorem_2_1_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:02:49.397427+00:00
-- url     : https://prove2.me/theorems/0460e01e-8a7f-4ad9-a6ea-c01eaf1c7440
-- title:
--   Theorem 2.1 (Könemann–Parekh–Pritchard), polynomial-time part: the rounding set J is computable in polynomial time
-- statement:
--   There is an algorithm, running in time polynomial in the binary length of a rationally encoded instance, with the following property. On every rationally encoded tree with positive integer capacities $c_e$, requests with nonempty paths and nonnegative weights $w_f$, and fractional values $x$ satisfying $0\le x_f\le 1$ and $\sum_{f:\,e\in\mathrm{Path}(f)}x_f\le c_e$ for every edge, it outputs a set $J$ of requests with
--   $$
--   \sum_{f\in J} w_f\ \ge\ \sum_f w_f x_f\qquad\text{and}\qquad \bigl|\{f\in J : e\in\mathrm{Path}(f)\}\bigr|\le c_e+2\ \text{for every } e.
--   $$
--
--   This is the "one can find, in polynomial time" clause of Theorem 2.1; the existence part is `TreeMultiflow.theorem_2_1`. It is the rounding step of the polynomial-time algorithm of Theorem 1.2.
--
--   **Formalization Note** The algorithm is a function on encoded instances computed by a Mathlib `TM2` Turing machine in polynomial time; its output is a Boolean mask over the requests. Its output is constrained only on well-formed inputs satisfying the hypotheses.
--
--   Differences from the source:
--   - reading: such a subset J can be found in polynomial time for rationally encoded inputs → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime encRatInstance id alg), correct on every well-formed instance with LP-feasible x; reason: the standard Turing-machine reading; numbers are binary, x is part of the input, and well-formedness excludes only inputs that are not trees with capacities ≥ 1 and weights ≥ 0
--   - encoding: capacities c_e, weights and x of a rationally encoded instance → the listed capacities, weights and x values of a RatInstance, read through RatInstance.graph/cap/src/dst/weight/lpval and the same IsLPFeasible and load as theorem_2_1; reason: same instances
--   - encoding: the subset J as the output of the algorithm → a Boolean mask alg I : List Bool, with f ∈ J iff (alg I).getD f false = true, so a missing entry means f ∉ J; vertices are Fin (n + 1); reason: a mask of length |F| is the usual output encoding of a subset, and every finite tree has such a labeling; same instances
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 2.1, p.4 (One can find, in polynomial time, …)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_TreeMultiflow_load
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

namespace TreeMultiflow

/-- **Theorem 2.1 (Könemann–Parekh–Pritchard), polynomial time.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 2.1,
p.4: "One can find, in polynomial time, a subset J of the requests such that Σ_{f∈J} w_f ≥
Σ_f w_f x_f and |{f ∈ J : e ∈ Path(f)}| ≤ cₑ + 2 for every e." (hypotheses as in
`theorem_2_1`: nonempty paths, positive integer capacities cₑ, nonnegative weights, x feasible).

There is a map `alg` from rational instances to request masks, computable by a Turing machine in
time polynomial in the length of the binary encoding `encRatInstance`, such that on every
well-formed instance (the listed capacities read as cₑ) whose requests have nonempty paths and
whose fractional values are feasible, the set `J` of requests `f` with `(alg I)[f] = true`
satisfies both conclusions of Theorem 2.1.

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with input encoding
`encRatInstance` (alphabet `OnlineCRS.Combine.Sym`, binary numbers) and output the mask itself
(alphabet `Bool`). The machine halts in polynomial time on every input; its output is constrained
only on the inputs described. Correctness is stated with the same `IsLPFeasible` and `load` as
`theorem_2_1`, for the instance decoded by `RatInstance.graph`, `cap`, `src`, `dst`, `weight`,
`lpval`. -/
theorem theorem_2_1_polytime :
    ∃ alg : RatInstance → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encRatInstance (fun m : List Bool => m) alg) ∧
      ∀ I : RatInstance, I.WellFormed → (∀ f, I.src f ≠ I.dst f) →
        IsLPFeasible I.graph I.cap I.src I.dst I.lpval →
        ∑ f, I.weight f * I.lpval f ≤
            ∑ f ∈ Finset.univ.filter (fun f : Fin I.reqs.length => (alg I).getD f false = true),
              I.weight f ∧
          ∀ e ∈ I.graph.edgeSet,
            load I.graph I.src I.dst
              (Finset.univ.filter fun f : Fin I.reqs.length => (alg I).getD f false = true) e ≤
              I.cap e + 2 := by sorry

end TreeMultiflow
