-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_theorem_1_5
-- name    : RoundedPotentials.Main.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:11:25.131689+00:00
-- url     : https://prove2.me/theorems/d9f93a5d-e395-49a0-8a81-aa93dc59696a
-- title:
--   Theorem 1.5 — Subquartic all-pairs verification (Corollary 4.10)
-- statement:
--   Directed All-Pairs Max-Flow, on general graphs with polynomially bounded capacities $W\le n^D$, has a nondeterministic algorithm with deterministic verification, in the total-function sense of Definition 2.3. Its running time is:
--
--   1. $n^{3.5+o(1)}$ if $\omega=2$: for every $\varepsilon>0$ there is such an algorithm running within $Cn^{7/2+\varepsilon}+C$ steps;
--   2. $O(n^{3.614})$ unconditionally: there is such an algorithm running within $Cn^{3.614}$ steps.
--
--   This resolves the general edge-capacity case of Trabelsi's question about subquartic nondeterministic algorithms for directed All-Pairs Max-Flow. The fastest known algorithm runs a max-flow computation for each pair, in $n^{4+o(1)}$ time.
--
--   **Formalization Note** Machine: `DynConnWC.Program` with `MinKCutII_Main_Runs`. $\omega$ is the published operational exponent `omega`. The unconditional clause uses the published bounds $\omega(2,1,1)\le3.250035$ and $\omega(2.5,1,1)\le3.720468$ only in its proof; they are not hypotheses.
--
--   Differences from the source:
--   - generalization: if ω = 2 (the matrix multiplication exponent) → if the published operational word-RAM exponent omega equals 2; reason: the operational exponent is at least 2 and at most the algebraic one, so the algebraic hypothesis ω = 2 implies this one
--   - encoding: n^{3.5+o(1)} time; O(n^{3.614}) time → ∀ ε > 0: C·n^{7/2+ε} + C steps; C·n^{3.614} steps (n ≥ 2); reason: explicit forms of the bounds
--   - encoding: nondeterministic algorithm with deterministic verification → NondetAPMF (Definition 2.3) on the word RAM DynConnWC.Program; reason: the paper's notion of nondeterministic time for a total function
--   - reading: general graphs → capacity matrices with entries ≤ W ≤ n^D, for every fixed D; reason: the standing polynomial bound of §1.1 and Table 1
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 6, Theorem 1.5

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Verification

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main DynConnWC MinKCutII.Main MultStretchAPASP.Weighted

theorem theorem_1_5 (D : ℕ) :
    -- `n^{3.5 + o(1)}` time if `ω = 2`
    (omega = 2 → ∀ ε : ℝ, 0 < ε → ∃ (P : Program) (C K : ℕ),
      ∀ (n W : ℕ), 2 ≤ n → 1 ≤ W → W ≤ n ^ D →
      ∀ (cap : Fin n → Fin n → ℕ), (∀ u v, cap u v ≤ W) →
        NondetAPMF P K n W cap (C * (n : ℝ) ^ ((7 : ℝ) / 2 + ε) + C)) ∧
    -- `O(n^{3.614})` time unconditionally
    (∃ (P : Program) (C K : ℕ),
      ∀ (n W : ℕ), 2 ≤ n → 1 ≤ W → W ≤ n ^ D →
      ∀ (cap : Fin n → Fin n → ℕ), (∀ u v, cap u v ≤ W) →
        NondetAPMF P K n W cap (C * (n : ℝ) ^ (3.614 : ℝ))) := by sorry

end RoundedPotentials.Main.Supplement
