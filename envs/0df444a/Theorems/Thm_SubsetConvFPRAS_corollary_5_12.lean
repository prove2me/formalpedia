-- Prove2me | Theorems.Thm_SubsetConvFPRAS_corollary_5_12
-- name    : SubsetConvFPRAS.corollary_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:41.125784+00:00
-- url     : https://prove2.me/theorems/3b6b93f9-0b2e-4320-b00d-24d2814f82d1
-- title:
--   Corollary 5.12 — choosing a field with $\pi_{t,z}(T=U\setminus S)\ge1/2$ in $O(n^{10}B^2\log 2B)$
-- statement:
--   Assume the standing hypotheses of §5 and put $t=1/(256n^2)$ and $B=2n+\lceil\log_2(R_\mu R_\nu)\rceil$. Given value oracles for $\mu,\nu$, upper bounds $R_\mu,R_\nu$ on the coefficient ranges and a supported pair $(S_0,T_0)$, there is one program of the arithmetic model and a constant $C$ such that, with $W=\lceil Cn^{10}B^2\log(2B)\rceil$:
--
--   1. every run halts within $W$ steps and either reports failure or returns a field $z\in\mathbb R^U_{>0}$;
--   2. on every run and at every step, the field register satisfies $\|\log z\|_1\le CnB$, (23);
--   3. if $Z_\cap>0$, then on at least a $31/32$ fraction of the tapes it returns a field with $\pi_{t,z}(T=U\setminus S)\ge1/2$.
--
--   The returned field is the one used by the estimator of Theorem 5.1.
--
--   **Formalization Note** Input: integer cell $0$ holds $n$, bitmaps $0,1$ hold $S_0,T_0$, real cells $0,1$ hold $R_\mu,R_\nu$; the field is real cell $2+u$. Output $1$ means a field was returned, output $0$ means failure. Before the program writes a cell of the field it holds $0$, and $\log0=0$ in Lean.
--
--   Differences from the source:
--   - generalization: the coefficient ranges R_μ, R_ν → any upper bounds R_μ, R_ν (RangeLE), with the bound in terms of them; reason: p.4 allows user-supplied upper bounds "with the same replacement in the running-time bounds"; R = the true range is a special case
--   - reading: an unnamed randomness primitive ("chooses with probability p") → fair coins only, one tape bit per coin instruction; reason: the page names no primitive for its arithmetic model; a unit-cost uniform real would be a stronger machine and so a weaker theorem
--   - encoding: an algorithm in the arithmetic model, O(·) operations and oracle calls → one admissible program of the unit-cost real RAM, with the constant C chosen before the instance and work counted per executed instruction; reason: the paper's model (p.44); every instruction costs 1, which only adds to the count
--   - encoding: every queried or returned field satisfies ‖log z‖₁ = O(nB) → the field register satisfies the bound at every step of every run, in particular at the end; reason: the queried fields are internal to an existential program and no clause can name them; the register is where the program keeps its current field
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Corollary 5.12, p.24 (proof pp.24–25)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_PairLaws
import Definitions.Def_SubsetConvFPRAS_Machine

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Corollary 5.12, p.24. With `t = 1/(256n²)` and
`B = 2n + ⌈log₂(R_μ R_ν)⌉`, one randomized program returns a field `z ∈ ℝ^U_{>0}` or reports failure. If `Z_∩ > 0`, with
probability at least `31/32` it returns a field with `π_{t,z}(T = U∖S) ≥ 1/2`. On every execution it uses
`O(n¹⁰ B² log(2B))` operations and oracle calls, and the field has `‖log z‖₁ = O(nB)`, (23).

**Formalization Note.** The input layout is `initField`. The program halts with output `1` for "field returned" and
`0` for failure, and the field register is `M (2+u)` (`fieldOf`). Queried fields are internal to a program, so (23) is
stated for the field register at every step, as well as at the end; before the program writes a cell it holds `0`, and
`Real.log 0 = 0`. -/
theorem corollary_5_12 :
    ∃ (P : Program) (C : ℕ), Admissible P ∧
      ∀ (n a b : ℕ) (μ ν : Finset (Fin n) → ℝ), IsHomogeneousPair a b μ ν →
      ∀ (S₀ T₀ : Finset (Fin n)) (Rμ Rν : ℝ), 0 < μ S₀ → 0 < ν T₀ → RangeLE μ Rμ → RangeLE ν Rν →
        let t : ℝ := 1 / (256 * (n : ℝ) ^ 2)
        let Bc : ℕ := 2 * n + ⌈Real.logb 2 (Rμ * Rν)⌉₊
        let W : ℕ := ⌈(C : ℝ) * (n : ℝ) ^ 10 * (Bc : ℝ) ^ 2 * Real.log (2 * (Bc : ℝ))⌉₊
        let s₀ := initField S₀ T₀ Rμ Rν
        (∀ ω : ℕ → Bool,
          (run P μ ν s₀ ω W).work ≤ W ∧
          ((run P μ ν s₀ ω W).output = some 0 ∨
            ((run P μ ν s₀ ω W).output = some 1 ∧ ∀ u, 0 < fieldOf (run P μ ν s₀ ω W) u)) ∧
          ∀ k ≤ W, ∑ u, |Real.log (fieldOf (run P μ ν s₀ ω k) u)| ≤ (C : ℝ) * (n : ℝ) * (Bc : ℝ)) ∧
        (0 < subsetConvTop μ ν →
          (31 / 32 : ℝ) * 2 ^ W ≤
            (tapeCount P μ ν s₀ W (fun st =>
              st.output = some 1 ∧ 1 / 2 ≤ complementMass μ ν (fun _ => t) (fieldOf st)) : ℝ)) := by sorry

end SubsetConvFPRAS
