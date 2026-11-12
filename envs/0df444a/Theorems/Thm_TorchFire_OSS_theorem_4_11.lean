-- Prove2me | Theorems.Thm_TorchFire_OSS_theorem_4_11
-- name    : TorchFire.OSS.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:40:52.590456+00:00
-- url     : https://prove2.me/theorems/300bf5ba-4900-4faa-9678-5d42fd91bc20
-- title:
--   Theorem 4.11 — strong one-bit OSS security: forging probability $O(\lambda^3k^3(q+2)^3/2^\lambda)$
-- statement:
--   For every quantum algorithm $A$ making at most $q$ queries to the oracles $(P,P^{-1},D)$ of Construction 4.2,
--   $$\Pr\Big[(b_0,u_0)\ne(b_1,u_1)\wedge\mathrm{OSS.Ver}^O(y,b_0,u_0)=\mathrm{OSS.Ver}^O(y,b_1,u_1)=1:\ O\leftarrow\mathrm{OSS.GenOracles}(1^\lambda),\ (y,b_0,u_0,b_1,u_1)\leftarrow A^O(1^\lambda)\Big]\le O\Big(\frac{\lambda^3k^3(q+2)^3}{2^\lambda}\Big).$$
--   The $O(\cdot)$ is an absolute constant $C>0$, the same for all $\lambda\ge2$, all $q$ and all algorithms. If $q$ is polynomial in $\lambda$, this gives strong OSS security (Definition 4.1): the forging probability is negligible.
--
--   The theorem is [SZ25, Theorem 30], cited without proof. It is used, through Lemma 8.4, to make the filtered modified acceptance $\varepsilon_\beta$ negligible.
--
--   Differences from the source:
--   - generalization: QPT adversaries → oracle algorithms with arbitrary finite workspace and unitaries; only the number of queries is bounded; reason: every QPT oracle algorithm is one with polynomially many queries (p.18); paper.md decision 2
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - reading: O(λ³k³(q+2)³/2^λ) → ∃ C > 0, ∀ λ ≥ 2, ∀ q, ∀ A with at most q queries; reason: paper.md decision 9
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Theorem 4.11, p.22 ([SZ25, Theorem 30])

import Mathlib
import Definitions.Def_TorchFire_OSS_longForgeProb
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model PPADSIS.SubexpSIS

namespace TorchFire.OSS

/-- **Theorem 4.11** (Construction 4.7 security, [SZ25, Theorem 30]), p.22 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). There is a constant
`C > 0` such that for every `λ ≥ 2`, every `q` and every quantum algorithm `A` making at most `q` queries
to `(P, P⁻¹, D)`, `Pr[(b_0, u_0) ≠ (b_1, u_1) ∧ OSS.Ver^O(y, b_0, u_0) = OSS.Ver^O(y, b_1, u_1) = 1]
≤ C · λ³k³(q + 2)³ / 2^λ`; and for polynomially many queries this is negligible (strong OSS security,
Definition 4.1). The source cites [SZ25] and gives no proof. -/
theorem theorem_4_11 :
    (∃ C : ℝ, 0 < C ∧ ∀ lam : ℕ, 2 ≤ lam → ∀ (q : ℕ) (A : OneForger lam), A.T ≤ q →
      oneForgeProb A ≤ C * (lam : ℝ) ^ 3 * (k lam : ℝ) ^ 3 * ((q : ℝ) + 2) ^ 3 / 2 ^ lam) ∧
    ∀ Q : ℕ → ℕ, PolyBounded Q → ∀ A : (lam : ℕ) → OneForger lam, (∀ lam, (A lam).T ≤ Q lam) →
      Negligible fun lam => oneForgeProb (A lam) := by sorry

end TorchFire.OSS
