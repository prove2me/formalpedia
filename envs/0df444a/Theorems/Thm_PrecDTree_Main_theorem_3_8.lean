-- Prove2me | Theorems.Thm_PrecDTree_Main_theorem_3_8
-- name    : PrecDTree.Main.theorem_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:53:17.145308+00:00
-- url     : https://prove2.me/theorems/84f0afe3-9031-471f-a886-6f957149e437
-- title:
--   Theorem 3.8 — an (α, β) f-PCSC approximation yields a polynomial-time O(α/log(5β/(5β−1)) · log n) PCWCDT approximation
-- statement:
--   If there is a polynomial-time bicriteria $(\alpha,\beta)$-approximation algorithm for f-PCSC, then there is a polynomial-time
--   $$O\!\left(\frac{\alpha}{\log\frac{5\beta}{5\beta-1}}\cdot\log n\right)\text{-approximation algorithm for PCWCDT.}$$
--   Formally: there is a universal constant $C>0$ such that for every ratio $\alpha$ (a function of the number $m$ of sets, evaluated at the instance's $m$) and every $\beta\ge1$, if one polynomial-time machine outputs on every valid f-PCSC instance a precedence-closed family covering at least $f\cdot n/\beta$ elements with at most $\alpha(m)\cdot\mathrm{OPT}$ sets, then one polynomial-time machine outputs on every PCWCDT instance $I=(H,T,\preceq)$ ($n=|H|\ge1$, $\preceq$ a partial order, every two hypotheses separated) a precedence-closed decision tree $D$ with
--   $$\mathrm{cost}_W(D)\ \le\ C\cdot\frac{\alpha(m)}{\log\frac{5\beta}{5\beta-1}}\cdot\log n\cdot\mathrm{OPT}(I).$$
--   The reduction is the paper's route from covering to decision trees; with Theorem 4.9 it gives Corollary 4.10.
--
--   **Formalization Note.** Logarithms are natural (`Real.log`); the ratio $\log n/\log\frac{5\beta}{5\beta-1}$ does not depend on the base.
--
--   Differences from the source:
--   - encoding: each test t ∈ T is a partition of H, and T is a family of m tests → tests are an indexed family T : Fin m → H → ℕ; the blocks of test t are the fibres of T t, restricted to the current hypothesis set; reason: every partition of a finite set is the fibre partition of a labelling by naturals; the instances are the same
--   - reading: polynomial-time algorithm (no machine model named) → one Mathlib Turing.TM2ComputableInPolyTime machine on binary words (PolyTimeBin), fixed before the instance, required to behave only on codes of valid instances; reason: the standard formal reading of a polynomial-time algorithm; the codes (encNat, incidence bits, tables) are of length polynomial in the input size
--   - reading: O(·) → an explicit universal constant C > 0, quantified before the algorithm and every instance; reason: 'O(g)-approximation' means cost ≤ C · g · OPT with C independent of the instance
--   - encoding: the algorithm outputs a decision tree → the machine's output is the binary code encodeTree I D of a tree D that is valid and precedence-closed for I; reason: the paper's algorithm outputs the explicit decision tree (p. 6); the code is a prefix code of the tree's nodes
--   - encoding: 0 < f ≤ 1 real in an f-PCSC instance → f rational in the encoded instance (PCSCInstance.f : ℚ); reason: an algorithm's input is finite; Algorithm 1 and the paper only use rational f (f = 1/4, f = t/n)
--   - generalization: α a number → α : ℕ → ℝ evaluated at the number m of sets (= tests) of the instance; reason: Corollary 4.10 needs α = O(m^{1/3}); a constant α is the special case α(m) ≡ α
--   - reading: β of the (α, β) ratio → hypothesis 1 ≤ β; reason: the paper's standing convention (p. 6: 'for β ≥ 1')
--   - reading: I = (H, T, ⪯) is an instance of the problem → hypotheses: ⪯ is a partial order (IsPartialOrderRel), H is nonempty, and every two distinct hypotheses are separated by some test (Identifiable); reason: the standing assumptions of §2 and the domain of the problem: without separation no decision tree exists and OPT is undefined (the proof of Lemma 3.4 uses it explicitly)
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 7, Theorem 3.8

import Mathlib
import Definitions.Def_PrecDTree_Main_Machine

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Theorem 3.8** (p. 7). If there is a polynomial-time bicriteria `(α, β)`-approximation
algorithm for f-PCSC, then there is a polynomial-time
`O(α / log(5β/(5β−1)) · log n)`-approximation algorithm for PCWCDT. The constant `C` of the `O(·)`
is universal: it is fixed before `α`, `β` and the instance. -/
theorem theorem_3_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℕ → ℝ) (β : ℝ), 1 ≤ β → HasPolyPCSCApprox α β →
      ∃ alg : List Bool → List Bool, PolyTimeBin alg ∧
        PCWCDTApprox (fun I => C * (α I.m / Real.log (5 * β / (5 * β - 1))) * Real.log (I.n : ℝ))
          alg := by sorry

end PrecDTree.Main
