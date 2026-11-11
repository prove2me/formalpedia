-- Prove2me | Theorems.Thm_SingleExpBisect_Main_theorem_1_1
-- name    : SingleExpBisect.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:41:46.301871+00:00
-- url     : https://prove2.me/theorems/e4fb693a-a6dc-447f-8c4b-0f6b8aa99aa8
-- title:
--   Theorem 1.1 — a (2k,k)-edge-unbreakable tree decomposition with adhesion ≤ 2k in O*(2^{O(k)}) time
-- statement:
--   There are a constant $C$ and one deterministic machine that, given any graph $G$ on $n$ vertices and any $k\ge0$, outputs within $C\cdot2^{Ck}\cdot(n+1)^C$ steps a rooted tree decomposition $T$ of $G$ whose adhesion is at most $2k$ and all of whose bags are $(2k,k)$-edge-unbreakable in $G$; moreover $T$ has at most $\max(n,1)$ nodes and every bag is nonempty when $n\ge1$.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph → SimpleGraph (Fin n) with vertex set Fin n; reason: Lean convention; every such graph is isomorphic to one on Fin n
--   - encoding: running time O*(·) on an unspecified machine → one deterministic TM2 machine (published OutputsWithin) and one constant C, both chosen before the instance, with the stated step bound in n = |V| and the parameter; reason: the paper names no machine model; O* suppresses factors polynomial in the input size, whose length is polynomial in n up to a log-of-parameter term absorbed by the exponential factor
--   - encoding: a (2k,k)-edge-unbreakable decomposition with adhesion at most 2k → published RootedTD output with encodeTD; IsRootedTreeDecomp (unique root + published tree-decomposition axioms on the parent-array tree), AdhesionLE T (2k), IsEdgeUnbreakableDecomp G T (2k) k; reason: Lean representation of a rooted tree decomposition
--   - generalization: no statement about empty bags → every bag is nonempty when n ≥ 1; reason: the construction (p. 35) puts {v} resp. v_C into every bag and Section 3 uses it (proof of Lemma 3.9); an added conclusion
--   - generalization: Theorem 1.1 does not state a node-count bound in its theorem sentence → T.N ≤ max n 1; reason: the construction on p. 35 has at most n recursive steps, as also used on p. 23; the empty graph has a one-node empty-bag decomposition; this adds a conclusion without removing any instance
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §1.1, p. 4, Theorem 1.1 (restated and proved p. 35)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), p. 4, Theorem 1.1 (proof p. 35): one
machine, given `G` and `k`, outputs within `C · 2^{C·k} · (n + 1)^C` steps a rooted tree
decomposition of `G` with adhesion at most `2k` all of whose bags are (2k, k)-edge-unbreakable in
`G`; it has at most `max n 1` nodes, and its bags are nonempty when `G` has a vertex
(the construction on p. 35; one empty bag suffices when `n = 0`). -/
theorem theorem_1_1 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ),
        ∃ T : RootedTD n,
          HMBinPacking.OutputsWithin M (encodeInput G k) (encodeTD T) (stepBound C k n) ∧
          IsRootedTreeDecomp G T ∧ AdhesionLE T (2 * k) ∧ IsEdgeUnbreakableDecomp G T (2 * k) k ∧
          T.N ≤ max n 1 ∧ (0 < n → ∀ t, (T.bag t).Nonempty) := by sorry

end SingleExpBisect.Main
