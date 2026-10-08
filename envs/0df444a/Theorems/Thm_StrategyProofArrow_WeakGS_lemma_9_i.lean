-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakGS_lemma_9_i
-- name    : StrategyProofArrow.WeakGS.lemma_9_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:55.809981+00:00
-- url     : https://prove2.me/theorems/6d05ce47-81f7-4a65-9a3d-440c207da1c7
-- title:
--   Lemma 9 (first sentence) — a regular tie-breaker followed by a strict strategy-proof procedure is strategy-proof
-- statement:
--   Consider a committee of $n\ge 1$ individuals and a finite set $S_m$ of $m\ge 3$ alternatives, with indifference admissible on ballots. Let $\nu:\rho_m^n\to S_m$ be a strict voting procedure that is strategy-proof (against substitutions of strong ballots), and let $\gamma:\pi_m^n\to\rho_m^n$ be a regular tie-breaking function. If the voting procedure $v:\pi_m^n\to S_m$ satisfies
--   $$v(B)=\nu[\gamma(B)]\qquad\text{for all } B\in\pi_m^n,$$
--   then $v$ is strategy-proof (against substitutions of arbitrary weak ballots).
--
--   Together with the second sentence of Lemma 9 it shows that regular composition with a tie-breaker relates strategy-proofness in strict and non-strict committees; it is one of the three lemmas on which the paper's §6 generalizations (Theorems 1′, 2′, 3′) rest.
--
--   **Formalization Note** The page prints the composition as $v^{nm}(B)=v^{nm}[\gamma(B)]$ with a Latin $v$ on the right, while the same sentence says "where $\nu^{nm}$ is a strict strategy-proof voting procedure" and the proof composes $\nu^{nm}$ with $\gamma$; we read the right-hand side as $\nu^{nm}[\gamma(B)]$. The hypotheses $n\ge 1$ and $m\ge 3$ are the paper's standing assumptions on a committee (p. 6).
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 9 (first sentence), p. 41

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic

namespace StrategyProofArrow.WeakGS

/-- **Lemma 9, first sentence** (Satterthwaite, p. 41). In a committee (`n ≥ 1`, `m ≥ 3`), if
`v(B) = ν[γ(B)]` for all `B ∈ π^n_m`, where `ν` is a strict strategy-proof voting procedure and `γ`
is a regular tie-breaking function, then `v` is strategy-proof. -/
theorem lemma_9_i {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : VotingProcedure ι A) (ν : StrictVotingProcedure ι A)
    (γ : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A)
    (hν : StrictStrategyProof ν) (hγ : IsRegularTieBreaking γ)
    (hv : ∀ B : WeakProfile ι A, v B = ν (γ B)) :
    StrategyProof v := by sorry

end StrategyProofArrow.WeakGS
