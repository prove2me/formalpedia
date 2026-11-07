-- Prove2me | Theorems.Thm_StableVotingDistortion_lemma_9
-- name    : StableVotingDistortion.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:05.539636+00:00
-- url     : https://prove2.me/theorems/2b9a78fe-8861-4787-a243-b23c8a23ea4a
-- title:
--   Lemma 9 (Upper Bound) — functions $\phi,\beta,c$ exist satisfying the Verifier Lemma with $1+2\lambda\le2.1248$
-- statement:
--   There exist $\lambda\in(0,1)$, $\phi$, $\beta$ and $c$ satisfying the hypotheses of the Verifier Lemma (Lemma 8) with
--   $$1+2\lambda\le2.1248.$$
--
--   This makes the Verifier Lemma's hypotheses nonvacuous at the value of $\lambda$ needed for the main theorem.
--
--   Differences from the source:
--   - reading: "the functions $\phi^\star$, $\beta$, and $c$ recorded in checker/certificate.json" → an existential over $\lambda,\phi,\beta,c$; reason: the certificate is outside the paper, and the existential is all the proof of Theorem 1 uses
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $\beta:(0,1)\to\mathbb R_{\ge0}$, $c:(0,1)\times[0,\lambda)\to\mathbb R_{\ge0}$ → total functions constrained only on those domains; reason: Lean functions are total; only printed arguments are used
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 9, p.31

import Mathlib
import Definitions.Def_StableVotingDistortion_VerifierHypotheses

set_option autoImplicit false

namespace StableVotingDistortion

/-- **Lemma 9 (Upper Bound).** There are `λ, ϕ, β, c` satisfying the hypotheses of Lemma 8 with
`1 + 2λ ≤ 2.1248`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 9, p.31: "The functions ϕ⋆, β, and c recorded in checker/certificate.json satisfy the
hypotheses of Lemma 8, with 1 + 2λ ≤ 2.1248."

**Formalization Note.** The certificate is not in the paper, so the functions are existentially quantified.
This is all the proof of Theorem 1 uses. The bound on `λ` is part of the statement: without it
`VerifierHypotheses` says nothing about `2.1248`. -/
theorem lemma_9 :
    ∃ (lam : ℝ) (ϕ β : ℝ → ℝ) (c : ℝ → ℝ → ℝ),
      VerifierHypotheses lam ϕ β c ∧ 1 + 2 * lam ≤ 2.1248 := by sorry

end StableVotingDistortion
