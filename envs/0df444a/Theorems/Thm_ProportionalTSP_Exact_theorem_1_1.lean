-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_theorem_1_1
-- name    : ProportionalTSP.Exact.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:29.432715+00:00
-- url     : https://prove2.me/theorems/5edfcfd0-4ee1-4232-a415-f7a42150997e
-- title:
--   Theorem 1.1 — Deterministic exact TSP below base two at the full fixed-alpha bound
-- statement:
--   For every fixed real $3/7<\alpha\le1/2$, a single deterministic program, independent of $\alpha$ and of the graph size, solves minimum-cost Hamiltonian cycle on every finite simple undirected graph containing an independent set of size at least $\alpha n$. Edge costs are arbitrary reals and may tie; edges may be absent. The attained exponential base is exactly
--   $$\gamma(\alpha)=\min_{z\ge1}2^{2\alpha-1}(2+z+z^2)^{1-\alpha}z^{-\alpha},\qquad0<\gamma(\alpha)<2.$$
--   There are $C>0$ and $d\in\mathbb N$, depending only on fixed $\alpha$, such that every promised input halts within $C(n+1)^d\gamma(\alpha)^n$ evaluated instructions and produces an actual optimal tour or a correct nonexistence answer. The program computes a maximum independent set within this same charged run; no independent set is supplied. Its syntax permits cost access only by copying, additions and comparisons.
--
--   For rational costs, the same program interpreted over $\mathbb Q$ has an additional bound $C_{\rm bit}(n+1)^{d_{\rm bit}}(B+1)^{e_{\rm bit}}\gamma(\alpha)^n$ in the defined bit-cost semantics, for total binary input length $B$. All constants and exponents precede the input quantifiers. The claim includes the tiny-size and nonexistence cases.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: Hamiltonian cycles counted as undirected cycles → finite unordered edge sets represented by a spanning simple cyclic list of length at least three; reason: rotations and reversal identify the same cycle, including in the parity count
--   - encoding: deterministic polynomial or O* running time → a finite RAM program, uniform positive coefficient and natural exponent, and its evaluated instruction count; reason: the explicit language charges combinatorial instructions and allows input reals only to be copied, added, and compared; signed values are pairs of sums
--   - encoding: O* also suppresses polynomial factors in the rational input bit length → the same finite program evaluated over rationals with an explicit operand-size cubic bit charge and a uniform polynomial factor in total binary input length; reason: accounts for rational numerator/denominator arithmetic and addressing rather than counting rational operations as unit cost
--   - generalization: an optional maximum-independent-set preprocessing is performed if R is absent, and the theorem's output is only the tour or nonexistence → the charged output must also expose a maximum independent set before the TSP answer; reason: the source algorithm computes this object within the bound on page 12; removing the prefix from the output gives the source claim
--   - encoding: gamma is the minimum in equation (1.1) → an existential positive gamma accompanied by an attained-minimum witness; reason: no total real infimum or arbitrary default value is used; the witness is a theorem conclusion, not an input
--   - generalization: Fix alpha; a deterministic algorithm (which may depend on alpha) → one program P quantified before alpha, with gamma, C and d chosen after alpha; reason: Algorithm 1 and its preprocessing never read alpha; instantiating alpha gives the source claim
--   - encoding: given an undirected graph with real edge costs; the algorithm finds a tour or reports none → input n, the adjacency matrix and a cost list with 0 at nonedges; output [0], or [1, v_0, ..., v_(n-1)] for a cycle order; reason: nonedge padding is never part of a tour cost and the output format decodes to the source answer
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Theorem 1.1, PDF p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem theorem_1_1 :
    ∃ P : RAM.Program, ∀ α : ℝ, 3/7 < α → α ≤ 1/2 →
      ∃ γ : ℝ, GammaValue α γ ∧ 0 < γ ∧ γ < 2 ∧
      ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∃ Cbit : ℝ, 0 < Cbit ∧ ∃ dbit ebit : ℕ,
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ), promised α G →
        ∃ t : ℕ, RAM.Halts P (graphInput G w) t ∧
          HeadlineOutput G w (RAM.run P (graphInput G w) t).out.reverse ∧
          (t : ℝ) ≤ C * (n+1)^d * γ^n) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ), promised α G →
        ∃ t : ℕ, RAM.Halts P (graphInput G w) t ∧
          HeadlineOutput G (fun e => (w e : ℝ)) (RAM.run P (graphInput G w) t).out.reverse ∧
          (RAM.bitTime P (graphInput G w) t : ℝ) ≤
            Cbit * (n+1)^dbit * (RAM.inputBits (graphInput G w)+1)^ebit * γ^n) := by sorry

end ProportionalTSP.Exact
