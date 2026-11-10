-- Prove2me | Theorems.Thm_PrecDTree_Main_corollary_4_10
-- name    : PrecDTree.Main.corollary_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:53:11.547256+00:00
-- url     : https://prove2.me/theorems/e82be5d3-d59e-4930-87b8-20d3aa15445c
-- title:
--   Corollary 4.10 — a polynomial-time O(m^{1/3} · log n)-approximation for worst-case decision trees under general precedence constraints
-- statement:
--   There is an $O(m^{1/3}\cdot\log n)$-approximation algorithm for PCWCDT running in polynomial time. Formally: there are a universal constant $C>0$ and one polynomial-time deterministic machine such that, on every PCWCDT instance $I=(H,T,\preceq)$ — a nonempty set $H$ of $n$ hypotheses, an indexed family $T$ of $m$ tests, each a partition of $H$, a partial order $\preceq$ on the tests, every two distinct hypotheses separated by some test — the machine outputs a decision tree $D$ for $I$ that is precedence-closed (at every node, every strict predecessor of each test on the root path occurs earlier on that path) and satisfies
--   $$\mathrm{cost}_W(D)\ \le\ C\cdot m^{1/3}\cdot\log n\cdot\mathrm{OPT}(I),$$
--   where $\mathrm{OPT}(I)$ is the minimum worst-case cost over all precedence-closed decision trees for $I$. This is the paper's headline algorithmic result for the worst-case objective under arbitrary precedence constraints.
--
--   **Formalization Note.** Natural logarithm (the base only changes $C$); $m^{1/3}$ is `(m : ℝ) ^ (1/3 : ℝ)`. Both sides vanish at $n=1$.
--
--   Differences from the source:
--   - encoding: each test t ∈ T is a partition of H, and T is a family of m tests → tests are an indexed family T : Fin m → H → ℕ; the blocks of test t are the fibres of T t, restricted to the current hypothesis set; reason: every partition of a finite set is the fibre partition of a labelling by naturals; the instances are the same
--   - reading: polynomial-time algorithm (no machine model named) → one Mathlib Turing.TM2ComputableInPolyTime machine on binary words (PolyTimeBin), fixed before the instance, required to behave only on codes of valid instances; reason: the standard formal reading of a polynomial-time algorithm; the codes (encNat, incidence bits, tables) are of length polynomial in the input size
--   - reading: O(·) → an explicit universal constant C > 0, quantified before the algorithm and every instance; reason: 'O(g)-approximation' means cost ≤ C · g · OPT with C independent of the instance
--   - encoding: the algorithm outputs a decision tree → the machine's output is the binary code encodeTree I D of a tree D that is valid and precedence-closed for I; reason: the paper's algorithm outputs the explicit decision tree (p. 6); the code is a prefix code of the tree's nodes
--   - reading: I = (H, T, ⪯) is an instance of the problem → hypotheses: ⪯ is a partial order (IsPartialOrderRel), H is nonempty, and every two distinct hypotheses are separated by some test (Identifiable); reason: the standing assumptions of §2 and the domain of the problem: without separation no decision tree exists and OPT is undefined (the proof of Lemma 3.4 uses it explicitly)
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 18, Corollary 4.10 (also p. 8, Corollary 3.9, third bullet)

import Mathlib
import Definitions.Def_PrecDTree_Main_Machine

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Corollary 4.10** (p. 18). There is an `O(m^{1/3} · log n)`-approximation algorithm for PCWCDT
running in polynomial time: a universal constant `C > 0` and one polynomial-time machine that, on
every valid PCWCDT instance, outputs a precedence-closed decision tree `D` with
`cost_W(D) ≤ C · m^{1/3} · log n · OPT(I)`. -/
theorem corollary_4_10 :
    ∃ C : ℝ, 0 < C ∧ ∃ alg : List Bool → List Bool, PolyTimeBin alg ∧
      PCWCDTApprox (fun I => C * (I.m : ℝ) ^ ((1 : ℝ) / 3) * Real.log (I.n : ℝ)) alg := by sorry

end PrecDTree.Main
