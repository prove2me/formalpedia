-- Prove2me | Theorems.Thm_TorchFire_TF_lemma_8_4
-- name    : TorchFire.TF.lemma_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:48:14.055695+00:00
-- url     : https://prove2.me/theorems/874f4160-4f58-496f-a620-df76f2d7fd31
-- title:
--   Lemma 8.4 — the filtered modified acceptance $\varepsilon_\beta$ is negligible
-- statement:
--   For every polynomially bounded integer $\beta\ge1$,
--   $$\varepsilon_\beta=\sum_{i=1}^N\mathbb E\big[\mathrm{Tr}(C_iL_i\rho_iL_iC_i^\dagger)\big]\le\mathrm{negl}(\lambda)\quad(90),$$
--   where local operators act as the identity on all other locations. Here, for a SPLIT adversary against Construction 7.4 with polynomially bounded $R,m,N$ ($m\le R$), polynomially many sparks and queries, $\rho$ is the joint input of the parties, $C_i$ the accepting map of party $i$ followed by verification of both its flames with $\Gamma$ replaced by $\Gamma^0_i$, $E_i$ the witness-sampler effect for the witness predicate (86) and a common bound $q$ on the query positions, and $L_i=(I-E_i)^\beta$.
--
--   The lemma says that once the challenge label's affine access is removed, a party that survives the filter cannot produce two accepted anchors; it bounds the $2\varepsilon_\beta$ term of (72).
--
--   Differences from the source:
--   - reading: the interactive game SPLIT in prose (adaptive spark queries, a torch request at any one point) → normal form: v spark flames issued first, one measured request J between two stages of A_0, entangled quantum registers B_i, probability Tr(T_{m+1}(Z_1..Z_N)ρ); reason: paper.md decision 4; simulates every adversary of Definition 6.2 with the same winning probability and query count
--   - generalization: QPT adversaries → oracle algorithms with arbitrary finite workspace and unitaries; only the number of queries is bounded; reason: every QPT oracle algorithm is one with polynomially many queries (p.18); paper.md decision 2
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - encoding: polynomially many spark queries → a polynomially bounded spark count v(λ); reason: normal form of the games
--   - encoding: polynomially bounded R, m, N with 0 ≤ m ≤ R → functions ℕ → ℕ, each PolyBounded, with m(λ) ≤ R(λ) for every λ; reason: paper.md decision 15
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: probabilities over oracle sampling, algorithmic randomness and measurement outcomes → averages over the uniform finite oracle sample of Tr(Eρ) for the final cq-state, measurements deferred (Fact 3.1); reason: paper.md decision 6
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
--   - reading: (90) as printed, Tr(L_i C_i† ρ_i C_i L_i) → (71)'s order Tr(C_i L_i ρ_i L_i C_i†); reason: paper.md decision 13: (90) does not type-check
--   - generalization: a common power-of-two bound q ≥ 1 on the local Γ-query positions, padded with invalid queries → any polynomially bounded q ≥ 1 that bounds every party's queries; padding positions contribute 0 to E_i; reason: the power of two serves only the implementation of a uniform j
--   - encoding: C_i = Π_i U^0_i J_i with coherent verification and its accepting projector → C_i†C_i as the acceptance effect of party i with Γ⁰_i followed by TF.Ver on both flames; reason: Tr(C_i L_i ρ_i L_i C_i†) depends on C_i only through C_i†C_i
--   - reading: ρ, "may be subnormalized due to setup aborts and label collisions" (p.69) → the joint input of the ideal experiment (setup abort and label collisions zeroed); reason: p.69
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 8.4, (90), p.72; §8.2 pp.69–71, (71)

import Mathlib
import Definitions.Def_TorchFire_TF_splitWinProb
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS PPADSIS.SubexpSIS

namespace TorchFire.TF

/-- **Lemma 8.4**, (90), p.72 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). For every polynomially bounded integer `β ≥ 1`,
`ε_β = Σ_{i=1}^N E[Tr(C_i L_i ρ_i L_i C_i†)] ≤ negl(λ)`, where local operators act as the identity on
all other locations: for polynomially bounded `R, m, N, v` with `m ≤ R`, every polynomially
query-bounded SPLIT adversary, and a polynomially bounded common bound `q ≥ 1` on the query positions
of the parties (padded with invalid queries). -/
theorem lemma_8_4 (R m N v Q q β : ℕ → ℕ) (hR : PolyBounded R) (hm : PolyBounded m)
    (hN : PolyBounded N) (hv : PolyBounded v) (hQ : PolyBounded Q) (hqp : PolyBounded q)
    (hβp : PolyBounded β) (hmR : ∀ lam, m lam ≤ R lam) (hβ : ∀ lam, 1 ≤ β lam)
    (hq : ∀ lam, 1 ≤ q lam ∧ Q lam ≤ q lam)
    (A : (lam : ℕ) → SplitAdv lam (R lam) (m lam) (N lam) (v lam))
    (hA : ∀ lam, (A lam).QueryBounded (Q lam)) :
    Negligible fun lam => epsSplit (A lam) (q lam) (β lam) := by sorry

end TorchFire.TF
