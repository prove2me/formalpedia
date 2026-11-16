-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_D_3
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:16:05.519513+00:00
-- url     : https://prove2.me/theorems/9090becc-8e5e-4390-b56f-e17ce646ee03
-- title:
--   Lemma D.3 (used in the proof of Theorem 4.4) — Exact square-root pruning bound
-- statement:
--   For every finite nonnegative monotone submodular technology, nonnegative costs and team $S$, a deterministic exact-real value-oracle pruning program returns a team $T\subseteq S$ and a feasible contract supporting $T$ as a pure Nash equilibrium, with total share at most one and
--   $$U_P(\alpha,T)\ge\left(\sqrt{f(S)}-W(S)/2\right)_+^2-\sum_{i\in S}c_i.$$
--   All zero-cost agents of $S$ can remain in $T$. The same program works for every instance, terminates, and uses at most $C(n+1)^2$ value queries for an absolute constant $C$. Empty teams, zero reward and rescaled rewards above one are included.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: deterministic value-oracle algorithms and arithmetic/query counts → a uniform finite rational-literal RAM program with an explicit query instruction, halted transcript and uniform numerical cost bounds; reason: the machine charges actual operations and queries without an optimization primitive; field-only programs implement numerical approximations internally, while D.3 uses the source exact-real convention
--   - encoding: O(n^2) value queries including the empty input and zero-cost agents may be kept fixed → an absolute C(n+1)^2 query budget and retention of every zero-cost member of S; reason: the additive one covers the finite empty input and makes the asymptotic bound meaningful there; this selects the fixed-free-agent version explicitly allowed by the source
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma D.3, printed p. 37 (PDF p. 39)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_OracleMachine

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma D.3, printed 37 / PDF 39. Exact-real arithmetic, quadratic queries. -/
theorem lemma_D_3 :
    ∃ (p : OracleProgram) (C : ℕ), Admissible p ∧ 0 < C ∧
      ∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ),
        IsTechnology f → (∀ i, 0 ≤ c i) → ∀ S : Finset (Fin n),
        ∃ steps : ℕ,
          Computes p f (machineInput c 0 0 0 0 S ∅ (fun _ => 0)) steps (C * (n + 1) ^ 2)
            (fun α T => T ⊆ S ∧ (∀ i ∈ S, c i = 0 → i ∈ T) ∧
              Supported f c α T ∧ IsEquilibrium f c α T ∧ (∑ i, α i) ≤ 1 ∧
              max (Real.sqrt (f S) - W c S / 2) 0 ^ 2 - (∑ i ∈ S, c i) ≤
                principalUtility f α T) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
