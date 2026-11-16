-- Prove2me | Theorems.Thm_TreeMultiflow_Supplement_theorem_3_1
-- name    : TreeMultiflow.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:52:37.839356+00:00
-- url     : https://prove2.me/theorems/a331af4d-aa9b-4e49-87ad-f4bcc7a4eff2
-- title:
--   Theorem 3.1: under bin conditions (i)–(iii), an eleven-colouring distinct within every bin with every colour class of load at most $u_e$
-- statement:
--   Let a tree have positive integer edge capacities $u_e$, and let a finite collection of labeled paths, each joining two distinct leaves, be given. At each leaf, suppose the paths ending there are partitioned into prescribed **bins**. Assume that
--
--   1. every bin contains at most six paths;
--   2. a leaf with incident edge $e$ has at most $u_e$ bins;
--   3. every internal edge $e$ (both endpoints of degree at least two) is used by at most $4u_e+2$ paths.
--
--   Then there is a colouring of the paths with eleven colours such that the paths within each prescribed bin receive pairwise distinct colours and, for every edge $e$ and every colour $i$, at most $u_e$ paths of colour $i$ use $e$.
--
--   This is the inductive form of Theorem 2.2: the bins at the leaves are part of the input and the colouring must respect them. Theorem 2.2 follows by forming bins of six consecutive paths at each leaf.
--
--   **Formalization Note** The hypotheses are the published `BinAssumptions`: bins are labels of path ends (a path $p$ has the end $(p,\mathrm{false})$ at $a(p)$ and $(p,\mathrm{true})$ at $b(p)$), and the bin of an end is the set of ends at the same leaf carrying the same label. Condition (ii) counts the distinct labels used at a leaf (the nonempty bins). Condition (iii) is on internal edges only, as printed. The tree is finite (`Fintype V`) and colours are `Fin 11`. The conclusion says that two different paths with ends at the same leaf in the same bin get different colours, and every colour class is feasible.
--
--   Differences from the source:
--   - encoding: prescribed bins partitioning the paths ending at each leaf → a label bin : P × Bool → κ on path ends, a bin being the ends at one leaf with one label; reason: a labeling of the ends is the same as a partition into nonempty bins, and a path has at most one end at each leaf
--   - encoding: a tree (finite) with a finite collection of labeled paths and eleven colours → [Fintype V], G.IsTree; a Fintype index type P with endpoints a, b; colours Fin 11; reason: same instances
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 3.1, p.6

import Mathlib
import Definitions.Def_TreeMultiflow_IsFeasible
import Definitions.Def_TreeMultiflow_pathEnd
import Definitions.Def_TreeMultiflow_BinAssumptions

namespace TreeMultiflow.Supplement

/-- **Theorem 3.1: eleven colours respecting prescribed bins.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 3.1,
p.6: "Let a tree have positive integer edge capacities uₑ, and let a finite collection of labeled
paths, each joining two distinct leaves, be given. At each leaf, suppose the paths ending there are
partitioned into prescribed bins. Assume that (i) every bin contains at most six paths; (ii) a leaf
with incident edge e has at most uₑ bins; (iii) every internal edge e is used by at most 4uₑ + 2
paths. There is an eleven-coloring such that the paths within each prescribed bin receive pairwise
distinct colors and, for every edge e, at most uₑ paths of any given color use e."

The hypotheses are `BinAssumptions` (leaf-to-leaf paths with distinct ends and conditions
(i)–(iii)); the conclusion is a colouring `c : P → Fin 11` such that two different paths with ends
in the same prescribed bin get different colours, and for every colour `i` the paths of colour
`i` form a feasible set (load at most `u e` on every edge `e`).

**Formalization Note.** The tree is finite (`[Fintype V]`), as for the ten-colour counterpart
`TreeMultiflow.theorem_5_2`; the paper's proof inducts on the number of internal vertices. Paths
are a finite index type `P` with endpoints `a`, `b`; bins are labels `bin : P × Bool → κ` of path
ends (`pathEnd`), and the bin of an end is the set of ends at the same leaf with the same label. -/
theorem theorem_3_1 {V P κ : Type*} [Fintype V] [Fintype P] (G : SimpleGraph V) (hG : G.IsTree)
    (u : Sym2 V → ℕ) (hu : ∀ e ∈ G.edgeSet, 1 ≤ u e) (a b : P → V) (bin : P × Bool → κ)
    (h : BinAssumptions G u a b bin) :
    ∃ c : P → Fin 11,
      (∀ ξ η : P × Bool, pathEnd a b ξ = pathEnd a b η → bin ξ = bin η → ξ.1 ≠ η.1 →
        c ξ.1 ≠ c η.1) ∧
      ∀ i : Fin 11, IsFeasible G u a b (Finset.univ.filter fun p => c p = i) := by sorry

end TreeMultiflow.Supplement
