-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_6
-- name    : PQNormIPM1352.Main.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:35.931314+00:00
-- url     : https://prove2.me/theorems/6436ef5c-bb09-46fe-9e17-ac17a3060091
-- title:
--   Lemma 6 — $K$ is convex and (6) is a $(3s+2)$-self-concordant barrier for $K$
-- statement:
--   Let $p \ge q > 1$ and let $A \in \mathbb R^{m\times n}$ be non-negative with support $S$, $s = |S|$, and no all-zero row or column. Let $K \subseteq \mathbb R^{m+n+s}$ be the feasible set of program (5),
--   $$K = \{(z,y,\gamma) : z \ge 0,\ y\ge 0,\ \textstyle\sum_i z(i)\le1,\ \sum_j y(j)\le1,\ |\gamma(i,j)| \le z(i)^{1/q^*}y(j)^{1/p}\ \forall (i,j)\in S\},$$
--   and let $F$ be the barrier (6). Then $K$ is convex and $F$ is a $\nu$-self-concordant barrier for $K$ with
--   $$\nu = 3s + 2,$$
--   in the sense of Definition 4: $K$ is closed and convex with nonempty interior, $F$ is smooth and self-concordant on $\mathrm{int}(K)$, diverges at the boundary of $K$, and $|\langle\nabla F(x),h\rangle| \le \sqrt{3s+2}\,\|h\|_x$ for every $x\in\mathrm{int}(K)$ and $h$.
--
--   This is the barrier the interior-point method of Algorithm 1 follows; $\nu$ governs its iteration count $O(\sqrt s\log(s/\varepsilon))$. The case $p = q$ is included.
--
--   Differences from the source:
--   - encoding: the non-negative matrix after removing all-zero rows and columns, a standing assumption of §3 (p. 7) → a sparsity pattern with every row and column occupied (`Preprocessed`) and the barrier on ℝ^{m+n+s}; reason: the paper removes such rows and columns before (5) and works with the support S only
--   - encoding: self-concordant barrier with complexity parameter ν (Definition 4, p. 5) → `IsNuSCB`: closed convex K with nonempty interior, F C^∞ and `ConvexOptimization.IsSelfConcordantOn` on int(K), divergence within int(K) at every frontier point, |DF(x)h| ≤ √ν‖h‖_x; reason: Definition 4 spelled out; the published line-restriction form of the cubic inequality is equivalent for C³ functions on an open set
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 6, printed p. 8 (PDF p. 9)

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Barrier

namespace PQNormIPM1352.Main

/-- **Lemma 6** (Pirazzini–Spielman, STOC 2027 #1352, p. 8). For `p ≥ q > 1` and a (preprocessed:
no all-zero row or column) sparsity pattern with `s` entries, the feasible set `K ⊆ ℝ^{m+n+s}` of
program (5) is convex, and the barrier (6) is a self-concordant barrier for `K` with complexity
parameter `ν = 3s + 2`. -/
theorem lemma_6 {m n s : ℕ} (P : SparsePattern m n s) (hP : P.Preprocessed) (p q : ℝ)
    (hq : 1 < q) (hqp : q ≤ p) :
    Convex ℝ (P.setK p q) ∧ IsNuSCB (P.setK p q) (P.barrierF p q) (nuParam s) := by sorry

end PQNormIPM1352.Main
