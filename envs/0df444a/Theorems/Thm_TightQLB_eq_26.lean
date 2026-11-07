-- Prove2me | Theorems.Thm_TightQLB_eq_26
-- name    : TightQLB.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:30.949346+00:00
-- url     : https://prove2.me/theorems/96ad9a20-8028-4917-9579-58984ba0f5e7
-- title:
--   §4.2, Eq. (26) — the score as a sum of squared norms, $B(\mathcal A)=\sum_z\|(b_z+b_z^\dagger)\Psi_z\|^2$
-- statement:
--   Let $\Psi_z=\Pi_z\Psi$ be the output-$z$ branch of the final state of a normal-form experiment. Then
--
--   $$
--   B(\mathcal A)=\sum_z\mathbb E_f\bigl[N\hat f(z)^2\|\Psi_z(f)\|^2\bigr]=\sum_z\bigl\|(b_z+b_z^\dagger)\Psi_z\bigr\|^2 .
--   $$
--
--   The average over $f$ is absorbed into the norm of $\mathcal F$, and the score becomes a sum of squared norms.
--
--   Differences from the source:
--   - encoding: "We fix an experiment …, which by Lemma 3.2 we may assume makes a fixed sequence of q controlled queries" (p. 21) → B : NormalForm n q (Qubits n × Bool) W E, for every finite W and E; reason: the paper's standing convention for §4; Lemma 3.2 (milestone) is the bridge
--   - generalization: "Throughout, n ≥ 1" (p. 13) → every n : ℕ, with no hypothesis on n; reason: the argument does not use n ≥ 1, and the instances with n ≥ 1 are the source's statement
--   - encoding: (b_z + b_z†)Ψ_z, as an operator sum applied to Ψ_z → bOp z Ψ_z + bOpAdj z Ψ_z; reason: the sum of operators applied to a vector; the same element of F
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §4.2, Eq. (26), p. 24 (PDF p. 27)

import Mathlib
import Definitions.Def_TightQLB_RecordingState

open QAlgorithms

namespace TightQLB

/-- **§4.2, Eq. (26) (the score as a sum of squared norms)**, p.24 (PDF p.27).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let Ψ_z = Π_zΨ be the output-z branch of the final state. … multiplication by √N f̂(z) is the
operator N^{−1/2} Σ_x χ_z(x)𝒳_x = b_z + b_z†. By (17) and this identity,
B(A) = Σ_z E_f[N f̂(z)² ‖Ψ_z(f)‖²] = Σ_z ‖(b_z + b_z†)Ψ_z‖²."

**Formalization Note.** `B` is an experiment in the normal form of Lemma 3.2. The two conjuncts are
the two equalities of (26), and `B.score` is (17) by definition. `n ≥ 1` is not needed. -/
theorem eq_26 {n q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (B : NormalForm n q (Qubits n × Bool) W E) :
    B.score = ∑ z, avgF (fun fb => (2 : ℝ) ^ n * idealDist fb z * ‖B.branch (valueOracle fb) z‖ ^ 2) ∧
    B.score = ∑ z, nsq (bOp z (B.branchFn z) + bOpAdj z (B.branchFn z)) := by sorry

end TightQLB
