-- Prove2me | Theorems.Thm_TorchFire_CGS_theorem_4_23
-- name    : TorchFire.CGS.theorem_4_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:44:39.686952+00:00
-- url     : https://prove2.me/theorems/b933e995-bb9f-4294-9f93-1852cb2ace4d
-- title:
--   Theorem 4.23 — CGS fire is verification-correct, cloning-correct and untelegraphable
-- statement:
--   Consider Construction 4.22 with the oracles of Construction 4.18 at security parameter $\mu$. Then
--
--   1. **verification correctness** (16): $\Pr[\mathrm{Fire.Ver}^O(pk,s,F)=1]\ge1-\mathrm{negl}(\mu)$ for an honest flame;
--   2. **cloning correctness** (17): for every polynomially bounded $q=q(\mu)$, after $q$ successive calls $(F_{i-1},F_i)\leftarrow\mathrm{Fire.Clone}^O(pk,s,F_{i-1})$ all $q+1$ flames verify with probability $1-\mathrm{negl}(\mu)$;
--   3. **untelegraphability** (18): for every pair $(A_1,A_2)$ making polynomially many queries in total, with a separable initial state and shared classical randomness, $A_1$ holding polynomially many spark flames, $A_2$ sending a classical $M$, $A_1$ a classical $L$, and $A_2$ outputting $(s^*,F^*)$,
--   $$\Pr[\mathrm{TELEGRAPH}^{\mathrm{Fire}}_{A^O}(1^\mu)=1]\le\mathrm{negl}(\mu).$$
--
--   The theorem is adapted from [ÇGS26, Theorems 16–17]; the source gives no proof. Torch-fire's correctness (through (52)) and its untelegraphability (Theorem 7.8) reduce to it.
--
--   Differences from the source:
--   - generalization: QPT adversaries → oracle algorithms with arbitrary finite workspace and unitaries; only the number of queries is bounded; reason: every QPT oracle algorithm is one with polynomially many queries (p.18); paper.md decision 2
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - reading: the interactive game TELEGRAPH in prose (separable start with shared randomness, adaptive spark queries) → normal form: shared randomness r with an adversary-chosen distribution, each party preparing its state from r; v flames first; messages M then L; reason: paper.md decision 5; finite separable states are finite mixtures of product states
--   - encoding: polynomially many spark queries → a polynomially bounded spark count v(λ); reason: normal form of the games
--   - encoding: probabilities over oracle sampling, algorithmic randomness and measurement outcomes → averages over the uniform finite oracle sample of Tr(Eρ) for the final cq-state, measurements deferred (Fact 3.1); reason: paper.md decision 6
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: any polynomially bounded ℓ ≥ r + k + 3 (21) → ℓ = r + k + 3; reason: the least allowed value; nothing depends on the choice
--   - encoding: OSS.Sign with intermediate measurements; U^O_{y,b} obtained from it by Fact 3.1 (Remark 4.12) → the deferred-measurement signing circuit written gate by gate; the zero state of Σ is |⊥⟩; reason: paper.md decisions 6 and 16
--   - reading: Fire.Gen^G: Construction 4.6 with its queries answered through G → the Construction 4.6 circuit; reason: by (22) G(enc(forward, x)) = P(x) and G(enc(inverse, y, u)) = P⁻¹(y, u): the same unitary
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Theorem 4.23, p.29 (adapted from [ÇGS26, Theorems 16–17]); Definitions 4.16–4.17 (16)–(18) pp.25–26

import Mathlib
import Definitions.Def_TorchFire_CGS_telegraphWinProb
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS PPADSIS.SubexpSIS

namespace TorchFire.CGS

/-- **Theorem 4.23** (correctness and untelegraphability, adapted from [ÇGS26, Theorems 16–17]), p.29
(Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). Construction 4.22 with the oracles of Construction 4.18 at security parameter `µ` satisfies
verification correctness (16) and cloning correctness (17) of Definition 4.16 (for every polynomially
bounded number `q` of cloning calls), and untelegraphability (18) of Definition 4.17 (for every
adversary pair making polynomially many queries in total, after polynomially many spark queries). The
source cites [ÇGS26] and gives no proof. -/
theorem theorem_4_23 :
    Negligible (fun mu => 1 - verCorr mu) ∧
    (∀ q : ℕ → ℕ, PolyBounded q → Negligible fun mu => 1 - cloneCorr mu (q mu)) ∧
    ∀ v Q : ℕ → ℕ, PolyBounded v → PolyBounded Q →
      ∀ A : (mu : ℕ) → TelegraphAdv mu (v mu), (∀ mu, (A mu).QueryBounded (Q mu)) →
        Negligible fun mu => telegraphWinProb (A mu) := by sorry

end TorchFire.CGS
