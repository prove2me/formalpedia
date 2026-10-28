-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_ext_marginal_stationary
-- name    : SluggishCapability.Myopic.ext_marginal_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:30.046245+00:00
-- url     : https://prove2.me/theorems/1cabcf5b-c674-44ab-9675-2f8b0b2a59b5
-- title:
--   Proof of Proposition 1, p. 17 — the extended chain is stochastic and its invariant laws have state marginal invariant for P
-- statement:
--   Let $P$ be a stochastic matrix on a finite set $S$, $f : S \to \mathbb{N}$ an output function and $M \ge \max_s f(s)$. Let $K$ be the extended kernel on pairs $(m, s)$ with $m \in \{0,\dots,M\}$: $K((m,s),(m',s')) = P(s,s')$ if $m' = g(m, f(s'))$ and $0$ otherwise, $g$ being the myopic update (2). Then
--
--   1. $K$ is a stochastic matrix;
--   2. for every invariant distribution $\nu$ of $K$, the state marginal $s \mapsto \sum_{m=0}^{M} \nu(m, s)$ is an invariant distribution of $P$.
--
--   Combined with uniqueness of the invariant distribution of an irreducible $P$, the marginal is $\lambda_P$, which is how the intensity constraint (1) enters the proof of Proposition 1.
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), p. 17, proof of Proposition 1 (extended process and its invariant distribution)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- Proof of Proposition 1, p. 17: the extended (capability, state) process is a Markov chain,
and the trainer-state marginal `s ↦ ∑_m ν(m, s)` of any of its invariant distributions `ν` is
invariant for `P`. -/
theorem ext_marginal_stationary {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (M : ℕ) (hP : IsStochastic P) (hM : ∀ s, f s ≤ M) :
    IsStochastic (extKernel P f M) ∧
    ∀ ν : Fin (M + 1) × S → ℝ, IsStationary (extKernel P f M) ν →
      IsStationary P (fun s => ∑ m : Fin (M + 1), ν (m, s)) := by sorry

end SluggishCapability.Myopic
