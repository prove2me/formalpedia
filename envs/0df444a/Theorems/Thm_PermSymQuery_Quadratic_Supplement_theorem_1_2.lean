-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_Supplement_theorem_1_2
-- name    : PermSymQuery.Quadratic.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:41:19.269789+00:00
-- url     : https://prove2.me/theorems/8fce79d9-d955-4b9e-b8da-86d8048e9bd6
-- title:
--   Theorem 1.2 — $R_\varepsilon(f)=O_k(Q_\varepsilon(f)^{2k})$ for k-uniform hypergraph properties
-- statement:
--   For every integer $k\ge2$ there is a positive natural constant $C_k$, depending only on $k$, such that for every natural number $N$, every promise $D$ of $k$-uniform hypergraphs on $[N]$, every $k$-uniform hypergraph property $f$ on $D$, and every $1/6\le\varepsilon<1/2$,
--   $$R_\varepsilon(f)\le C_k\,Q_\varepsilon(f)^{2k}.$$
--   Both complexities have error at most $\varepsilon$ on every promised input and worst-case cost. The quantum algorithm queries the ordered-tuple oracle $O_H$ with any finite workspace; the randomized algorithm makes hyperedge-membership queries. The constant does not depend on $N$, the promise, the property or the error. The case $Q_\varepsilon(f)=0$ is included.
--
--   For $k=2$ this is the quartic bound $R_\varepsilon(f)=O(Q_\varepsilon(f)^4)$ for graph properties in the adjacency-matrix model. It is a companion theorem to the mission's string result, Theorem 1.1, and is not used in its proof.
--
--   Differences from the source:
--   - encoding: vertex set [N], ordered vertex tuples, one answer bit and signed outputs → Fin N, Fin k → Fin N, ZMod 2, and output probabilities of true and false; reason: these relabel the vertices and registers and preserve the signed expectation Pr[1] − Pr[0]
--   - encoding: arbitrary finite quantum workspaces and two-outcome measurements → published QueryAlg with an arbitrary finite workspace and a Boolean computational-basis output map; reason: input-independent final unitaries and ancillary registers realize every source measurement without additional queries (the base mission's convention)
--   - encoding: a partial k-uniform hypergraph property f : D ⊆ {0,1}^([N] choose k) → {0,1} → a Bool-valued function on all hypergraphs with HypPermInvariant D f, used only on D; reason: the values of f outside D are never read; every source instance, including the empty promise, is represented
--   - encoding: minimum worst-case query budgets and an O_k(·) bound → infima in ℕ∞ and, for each k ≥ 2, one positive natural constant quantified before every other datum; reason: an infeasible budget set gives infinity, every nonempty set of natural budgets has a least element, and rounding a positive constant up preserves the bound
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Theorem 1.2 (stated PDF p. 4, printed p. 2), restated, PDF p. 24 (printed p. 22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Supplement_Hypergraph

namespace PermSymQuery.Quadratic.Supplement

/-- Theorem 1.2, PDF p.4 (printed p.2), restated PDF p.24 (printed p.22): for each `k ≥ 2` one
constant `C_k`, independent of `N`, the promise, the property and the error. -/
theorem theorem_1_2 : ∀ k : ℕ, 2 ≤ k → ∃ C : ℕ, 0 < C ∧
    ∀ (N : ℕ) (D : Set (Hypergraph (Fin N) k)) (f : Hypergraph (Fin N) k → Bool),
      HypPermInvariant D f →
    ∀ ε : ℝ, 1 / 6 ≤ ε → ε < 1 / 2 →
      HReps D f ε ≤ (C : ℕ∞) * (HQeps D f ε) ^ (2 * k) := by sorry

end PermSymQuery.Quadratic.Supplement
