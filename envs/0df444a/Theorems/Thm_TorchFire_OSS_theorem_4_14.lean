-- Prove2me | Theorems.Thm_TorchFire_OSS_theorem_4_14
-- name    : TorchFire.OSS.theorem_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:23.506031+00:00
-- url     : https://prove2.me/theorems/a1f246be-23b4-4383-9858-89c525098e03
-- title:
--   Theorem 4.14 — long-message OSS (Construction 4.13) is correct and strongly one-shot secure on $\{0,1\}^{\le p(\lambda)}$
-- statement:
--   Let $p:\mathbb N\to\mathbb N$ be a polynomial in $\lambda$ and set the message space to $\mathcal M_\lambda=\{0,1\}^{\le p(\lambda)}$. Then the scheme of Construction 4.13 satisfies
--
--   1. **correctness** (2): for every message $M\in\mathcal M_\lambda$, sampling the oracles, generating a key, signing $M$ and verifying succeeds with probability $1-\mathrm{negl}(\lambda)$;
--   2. **strong one-shot security** (3): for every quantum adversary making polynomially many total oracle queries,
--   $$\Pr\big[(M_0,\sigma_0)\ne(M_1,\sigma_1)\wedge\mathrm{OSS.Ver}^O(a,M_0,\sigma_0)=\mathrm{OSS.Ver}^O(a,M_1,\sigma_1)=1\big]\le\mathrm{negl}(\lambda).$$
--
--   The theorem is adapted from [SZ25, Theorem 30] and [HSVZ26, Lemma 71]; the source obtains it by combining Theorems 4.10 and 4.11 and gives no proof. It is the security of the torches, used in Lemma 8.5.
--
--   Differences from the source:
--   - generalization: QPT adversaries → oracle algorithms with arbitrary finite workspace and unitaries; only the number of queries is bounded; reason: every QPT oracle algorithm is one with polynomially many queries (p.18); paper.md decision 2
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: OSS.Sign with intermediate measurements; U^O_{y,b} obtained from it by Fact 3.1 (Remark 4.12) → the deferred-measurement signing circuit written gate by gate; the zero state of Σ is |⊥⟩; reason: paper.md decisions 6 and 16
--   - encoding: the message space {0,1}^{≤p(λ)} → pairs of a length m ≤ p(λ) and a string in {0,1}^m; reason: the same set
--   - reading: "for every m ∈ M_λ, Pr ≥ 1 − negl(λ)" → for every λ-indexed choice of messages; reason: the message may depend on λ
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Theorem 4.14, p.23 (adapted from [SZ25, Theorem 30], [HSVZ26, Lemma 71])

import Mathlib
import Definitions.Def_TorchFire_OSS_longForgeProb
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model PPADSIS.SubexpSIS

namespace TorchFire.OSS

/-- **Theorem 4.14** (long-message correctness and strong security, adapted from [SZ25, Theorem 30] and
[HSVZ26, Lemma 71]), p.23 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). For a polynomially bounded `p` and the message space
`M_λ = {0,1}^{≤p(λ)}`, Construction 4.13 satisfies correctness (2) for every message, and strong
one-shot security (3) against every adversary making polynomially many total oracle queries. The
source derives it from Theorems 4.10 and 4.11 and gives no proof. -/
theorem theorem_4_14 (p : ℕ → ℕ) (hp : PolyBounded p) :
    (∀ M : (lam : ℕ) → BitStr (p lam), Negligible fun lam => 1 - longCorrProb lam (M lam)) ∧
    ∀ Q : ℕ → ℕ, PolyBounded Q → ∀ A : (lam : ℕ) → LongForger lam (BitStr (p lam)),
      (∀ lam, (A lam).T ≤ Q lam) → Negligible fun lam => longForgeProb (A lam) := by sorry

end TorchFire.OSS
