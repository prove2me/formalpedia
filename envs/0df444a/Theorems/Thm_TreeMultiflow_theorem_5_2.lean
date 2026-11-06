-- Prove2me | Theorems.Thm_TreeMultiflow_theorem_5_2
-- name    : TreeMultiflow.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:54.171962+00:00
-- url     : https://prove2.me/theorems/d12cfed8-02ec-46ff-9bc9-81d3431fe1b2
-- title:
--   Theorem 5.2: under the assumptions of Theorem 3.1, ten colours suffice
-- statement:
--   Let a tree have positive integer edge capacities $u_e$, and let a finite collection of labeled paths, each joining two distinct leaves, be given. At each leaf, suppose the paths ending there are partitioned into prescribed bins, and assume that
--
--   1. (i) every bin contains at most six paths;
--   2. (ii) a leaf with incident edge $e$ has at most $u_e$ bins;
--   3. (iii) every internal edge $e$ is used by at most $4u_e+2$ paths.
--
--   Then ten colours suffice: there is a colouring of the paths with ten colours such that the paths in each prescribed bin receive distinct colours, and each edge $e$ is used by at most $u_e$ paths of any one colour.
--
--   This is the ten-colour colouring theorem behind the $2/5$ bound of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: a tree (finite; the proof inducts on |E|) → [Fintype V] with G.IsTree; reason: same instances
--   - encoding: paths partitioned into prescribed bins at each leaf → a label bin ξ of every path end ξ (BinAssumptions); ten colours as Fin 10; reason: a labeling of the ends is a partition into nonempty bins
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 5.2, p.9 (under the assumptions of Theorem 3.1, p.6)

import Mathlib
import Definitions.Def_TreeMultiflow_IsFeasible
import Definitions.Def_TreeMultiflow_pathEnd
import Definitions.Def_TreeMultiflow_BinAssumptions

namespace TreeMultiflow

/-- **Theorem 5.2: ten colours suffice.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 5.2,
p.9: "Under the assumptions of Theorem 3.1, ten colors suffice: the paths in each prescribed bin
receive distinct colors, and each edge e is used by at most uₑ paths of any one color." The
assumptions of Theorem 3.1 (p.6): a tree with positive integer edge capacities uₑ, a finite
collection of labeled paths, each joining two distinct leaves, prescribed bins at each leaf, and
(i) every bin contains at most six paths; (ii) a leaf with incident edge e has at most uₑ bins;
(iii) every internal edge e is used by at most 4uₑ + 2 paths (`BinAssumptions`).

The conclusion: a colouring `c : P → Fin 10` such that two different paths with ends in the same
prescribed bin get different colours, and for every colour `i` the paths of colour `i` form a
feasible set (load at most `u e` on every edge `e`).

**Formalization Note.** The tree is finite (`[Fintype V]`), as in the paper, whose proof
inducts on `|E|`. Paths are a finite index type `P` with endpoints `a`, `b`; bins are labels of
path ends (`BinAssumptions`). -/
theorem theorem_5_2 {V P κ : Type*} [Fintype V] [Fintype P] (G : SimpleGraph V) (hG : G.IsTree)
    (u : Sym2 V → ℕ) (hu : ∀ e ∈ G.edgeSet, 1 ≤ u e) (a b : P → V) (bin : P × Bool → κ)
    (h : BinAssumptions G u a b bin) :
    ∃ c : P → Fin 10,
      (∀ ξ η : P × Bool, pathEnd a b ξ = pathEnd a b η → bin ξ = bin η → ξ.1 ≠ η.1 →
        c ξ.1 ≠ c η.1) ∧
      ∀ i : Fin 10, IsFeasible G u a b (Finset.univ.filter fun p => c p = i) := by sorry

end TreeMultiflow
