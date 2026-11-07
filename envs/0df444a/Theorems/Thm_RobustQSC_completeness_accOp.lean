-- Prove2me | Theorems.Thm_RobustQSC_completeness_accOp
-- name    : RobustQSC.completeness_accOp
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:01.914204+00:00
-- url     : https://prove2.me/theorems/06efd2fa-135f-4e73-8302-46d62518309c
-- title:
--   §4, p.20 — completeness: $\mathrm{Tr}[A\rho]\ge\langle\psi|\rho|\psi\rangle$
-- statement:
--   Let $n\ge1$. For every pure target state $|\psi\rangle$ and every density matrix $\rho$,
--
--   $$
--   \mathrm{Tr}[A\rho]\ge\langle\psi|\rho|\psi\rangle,
--   $$
--
--   where $A$ is the acceptance operator of $|\psi\rangle$. This is the completeness half of Theorem 1, and it holds for every target, not only for almost every one.
--
--   Differences from the source:
--   - reading: the post-measurement states are undefined on zero fibres → the corresponding term of $A$ is $0$; reason: $|\psi\rangle$ is still an eigenvector of eigenvalue $1$ under this convention, so the printed claim holds for every unit target
--   - encoding: $\langle\psi|\rho|\psi\rangle$ → `effectProb (pureDensity ψ) ρ`, the real part of $\mathrm{Tr}(|\psi\rangle\langle\psi|\rho)$; reason: same quantity
--   - encoding: $n$ qubits, $A$ the operator of Protocol 1 → hypothesis $n\ge1$; reason: $A$ has the factor $1/(2n)$ and a holdout qubit $i\in[n]$; at $n=0$ there is no protocol
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §4, p.20

import Definitions.Def_RobustQSC_accOp

namespace RobustQSC

open QAlgorithms

/-- **§4, completeness (p.20).** For every target state `|ψ⟩` and every lab state `ρ`,
`Tr[Aρ] ≥ ⟨ψ|ρ|ψ⟩`, `A` the acceptance operator of Protocol 1.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), §4, p.20 ("Since |ψ⟩ itself is an eigenvector of A with eigenvalue +1, we have
Tr[A|ϕ⟩⟨ϕ|] ≥ |⟨ψ|ϕ⟩|². This extends to mixed lab states ρ, to give Tr[Aρ] ≥ ⟨ψ|ρ|ψ⟩").

**Formalization Note.** `⟨ψ|ρ|ψ⟩ = effectProb (pureDensity ψ) ρ`; `n ≥ 1` (at `n = 0` there is
no protocol and `accOp = 0`). -/
theorem completeness_accOp (n : ℕ) (hn : 1 ≤ n) (ψ : EuclideanSpace ℂ (Qubits n))
    (hψ : IsState ψ) (ρ : Matrix (Qubits n) (Qubits n) ℂ) (hρ : IsDensityMatrix ρ) :
    effectProb (pureDensity ψ) ρ ≤ effectProb (accOp ψ) ρ := by sorry

end RobustQSC
