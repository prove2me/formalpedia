-- Prove2me | Theorems.Thm_TightQLB_lemma_4_4
-- name    : TightQLB.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:38.76104+00:00
-- url     : https://prove2.me/theorems/46c57d07-1b8c-4901-8c09-2c2e1aa64fa0
-- title:
--   Lemma 4.4 — growth bound, $\lambda(\Psi_{t+1})\le\lambda(\Psi_t)+2\sqrt{t/N}$ and $\lambda(\Psi)\le\frac43q^{3/2}/\sqrt N$
-- statement:
--   For $0\le t<q$,
--
--   $$
--   \lambda(\Psi_{t+1})\le\lambda(\Psi_t)+2\sqrt{t/N}.
--   $$
--
--   Consequently,
--
--   $$
--   \lambda(\Psi)\le\bar\lambda_q:=\frac2{\sqrt N}\sum_{t=0}^{q-1}\sqrt t\le\frac43\cdot\frac{q^{3/2}}{\sqrt N}.
--   $$
--
--   So one query made after $t$ earlier queries raises the progress measure by at most $2\sqrt{t/N}$, and $q$ queries raise it from $0$ to order $q^{3/2}/\sqrt N$.
--
--   Differences from the source:
--   - encoding: "We fix an experiment …, which by Lemma 3.2 we may assume makes a fixed sequence of q controlled queries" (p. 21) → B : NormalForm n q (Qubits n × Bool) W E, for every finite W and E; reason: the paper's standing convention for §4; Lemma 3.2 (milestone) is the bridge
--   - generalization: "Throughout, n ≥ 1" (p. 13) → every n : ℕ, with no hypothesis on n; reason: the argument does not use n ≥ 1, and the instances with n ≥ 1 are the source's statement
--   - encoding: q^{3/2}, and t, q as real quantities → Real.rpow, and natural numbers cast to ℝ; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Lemma 4.4, p. 26 (PDF p. 29), Eq. (34)

import Mathlib
import Definitions.Def_TightQLB_RecordingState

open QAlgorithms

namespace TightQLB

/-- **Lemma 4.4 (Growth bound)**, p.26 (PDF p.29), Eq. (34).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"For 0 ≤ t < q, λ(Ψ_{t+1}) ≤ λ(Ψ_t) + 2√(t/N). Consequently,
λ(Ψ) ≤ λ̄_q := (2/√N) Σ_{t=0}^{q−1} √t ≤ (4/3) · q^{3/2}/√N."

**Formalization Note.** `B` is an experiment in the normal form of Lemma 3.2, `Ψ_t = B.stateFn t`
(indexed by `Fin (q + 1)`) and `Ψ = B.finalFn`. The three clauses are the step bound, the bound by
`λ̄_q` and the bound on `λ̄_q`. `q^{3/2}` is `Real.rpow`; `N = 2^n`; `n ≥ 1` is not needed. -/
theorem lemma_4_4 {n q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (B : NormalForm n q (Qubits n × Bool) W E) :
    (∀ (t : ℕ) (h : t < q),
      lam (B.stateFn ⟨t + 1, by omega⟩) ≤
        lam (B.stateFn ⟨t, by omega⟩) + 2 * Real.sqrt ((t : ℝ) / (2 : ℝ) ^ n)) ∧
    lam B.finalFn ≤ 2 / Real.sqrt ((2 : ℝ) ^ n) * ∑ t ∈ Finset.range q, Real.sqrt (t : ℝ) ∧
    2 / Real.sqrt ((2 : ℝ) ^ n) * ∑ t ∈ Finset.range q, Real.sqrt (t : ℝ) ≤
      4 / 3 * (q : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt ((2 : ℝ) ^ n) := by sorry

end TightQLB
