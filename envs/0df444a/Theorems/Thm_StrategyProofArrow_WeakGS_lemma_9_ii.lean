-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakGS_lemma_9_ii
-- name    : StrategyProofArrow.WeakGS.lemma_9_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:03.540545+00:00
-- url     : https://prove2.me/theorems/ca38481f-c005-44a1-8b7b-018ddfbc2132
-- title:
--   Lemma 9 (second sentence) — every strategy-proof procedure is a tie-breaker followed by a strict strategy-proof procedure
-- statement:
--   Consider a committee of $n\ge 1$ individuals and a finite set $S_m$ of $m\ge 3$ alternatives, with indifference admissible on ballots. If the voting procedure $v:\pi_m^n\to S_m$ is strategy-proof, then there exist a strict strategy-proof voting procedure $\nu:\rho_m^n\to S_m$ and a tie-breaking function $\alpha:\pi_m^n\to\rho_m^n$ such that
--   $$v(B)=\nu[\alpha(B)]\qquad\text{for all } B\in\pi_m^n.$$
--
--   The tie-breaking function $\alpha$ need not be regular: $\alpha(B)_i$ may depend on the whole ballot set $B$, not only on $B_i$. This decomposition reduces the case of ballots with indifference to the strict case, and is the step that carries Theorem 1 over to Theorem 1′.
--
--   **Formalization Note** A tie-breaking function only has to keep every strict preference of every ballot; no regularity is required. The hypotheses $n\ge 1$ and $m\ge 3$ are the paper's standing assumptions on a committee (p. 6).
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 9 (second sentence), p. 41

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic

namespace StrategyProofArrow.WeakGS

/-- **Lemma 9, second sentence** (Satterthwaite, p. 41). In a committee (`n ≥ 1`, `m ≥ 3`), if the
voting procedure `v` is strategy-proof, then there exist a strict strategy-proof voting procedure
`ν` and a tie-breaking function `α` (not necessarily regular) with `v(B) = ν[α(B)]` for all
`B ∈ π^n_m`. -/
theorem lemma_9_ii {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : VotingProcedure ι A) (hv : StrategyProof v) :
    ∃ (ν : StrictVotingProcedure ι A) (α : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A),
      StrictStrategyProof ν ∧ IsTieBreaking α ∧ ∀ B : WeakProfile ι A, v B = ν (α B) := by sorry

end StrategyProofArrow.WeakGS
