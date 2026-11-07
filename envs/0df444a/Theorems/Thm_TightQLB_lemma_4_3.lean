-- Prove2me | Theorems.Thm_TightQLB_lemma_4_3
-- name    : TightQLB.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:13.214846+00:00
-- url     : https://prove2.me/theorems/a3e1d19b-c836-4b61-92f6-49cea89996b2
-- title:
--   Lemma 4.3 — score bound, $B(\mathcal A)\le3-\frac2N+2\lambda+2(1-\frac1N)\lambda^2-2(1-\frac1N)\sum_z\|(D_z-I)\Psi_z\|^2$
-- statement:
--   Let $\Psi$ be the final state of the experiment, let $\Psi_z=\Pi_z\Psi$ be its output-$z$ branches, and let $\lambda=\lambda(\Psi)$. Then
--
--   $$
--   B(\mathcal A)\le3-\frac2N+2\lambda+2\Bigl(1-\frac1N\Bigr)\lambda^2-2\Bigl(1-\frac1N\Bigr)\sum_z\bigl\|(D_z-I)\Psi_z\bigr\|^2 .
--   $$
--
--   So the score exceeds the ideal score $3-2/N$ by at most $2\lambda+2\lambda^2$. Note that $\lambda$ is evaluated on the whole state and the last sum on the branches.
--
--   Differences from the source:
--   - encoding: "We fix an experiment …, which by Lemma 3.2 we may assume makes a fixed sequence of q controlled queries" (p. 21) → B : NormalForm n q (Qubits n × Bool) W E, for every finite W and E; reason: the paper's standing convention for §4; Lemma 3.2 (milestone) is the bridge
--   - generalization: "Throughout, n ≥ 1" (p. 13) → every n : ℕ, with no hypothesis on n; reason: the argument does not use n ≥ 1, and the instances with n ≥ 1 are the source's statement
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Lemma 4.3, p. 24 (PDF p. 27), Eq. (30)

import Mathlib
import Definitions.Def_TightQLB_RecordingState

open QAlgorithms

namespace TightQLB

/-- **Lemma 4.3 (Score bound)**, p.24 (PDF p.27), Eq. (30).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let Ψ be the final state of the experiment, let Ψ_z = Π_zΨ be its output-z branches, and let
λ = λ(Ψ). Then B(A) ≤ 3 − 2/N + 2λ + 2(1 − 1/N)λ² − 2(1 − 1/N) Σ_z ‖(D_z − I)Ψ_z‖²."

**Formalization Note.** `B` is an experiment in the normal form of Lemma 3.2; `λ` is evaluated on the
whole final state `B.finalFn`, and the last sum on the branches `B.branchFn z`. `N = 2^n`;
`n ≥ 1` is not needed. -/
theorem lemma_4_3 {n q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (B : NormalForm n q (Qubits n × Bool) W E) :
    B.score ≤ 3 - 2 / (2 : ℝ) ^ n + 2 * lam B.finalFn
        + 2 * (1 - 1 / (2 : ℝ) ^ n) * lam B.finalFn ^ 2
        - 2 * (1 - 1 / (2 : ℝ) ^ n) *
          ∑ z, nsq (bOpAdj z (bOp z (B.branchFn z)) - B.branchFn z) := by sorry

end TightQLB
