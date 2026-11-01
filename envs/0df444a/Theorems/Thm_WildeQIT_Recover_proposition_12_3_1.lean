-- Prove2me | Theorems.Thm_WildeQIT_Recover_proposition_12_3_1
-- name    : WildeQIT.Recover.proposition_12_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:22:10.747006+00:00
-- url     : https://prove2.me/theorems/d3ba714f-d79f-4585-a957-b3840b588df4
-- title:
--   Proposition 12.3.1 (Perfect Recovery) — $\mathcal R^t_{\sigma,\mathcal N}(\mathcal N(\sigma))=\sigma$
-- statement:
--   Let $\sigma$ be a positive semi-definite operator on a finite-dimensional Hilbert space $\mathcal H$ and $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ a quantum channel. For every $t\in\mathbb R$ the rotated Petz map recovers $\sigma$ from $\mathcal N(\sigma)$:
--
--   $$
--   \mathcal R^t_{\sigma,\mathcal N}(\mathcal N(\sigma))=\sigma .
--   $$
--
--   No invertibility of $\sigma$ is assumed; all powers of $\sigma$ and $\mathcal N(\sigma)$ are taken on their supports. This property makes the recoverability bound nontrivial: the recovery maps in it always restore $\sigma$ exactly.
--
--   **Formalization Note** The channel is given by a finite family of Kraus operators.
--
--   Differences from the source:
--   - encoding: a quantum channel → a channel in Choi–Kraus form; reason: every channel has a Kraus form with finitely many operators (Theorem 4.4.1), and the statement does not depend on the family.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Proposition 12.3.1, (12.38), p. 372

import Definitions.Def_WildeQIT_Recover_rotatedPetz
open scoped ComplexOrder

namespace WildeQIT.Recover

/-- **Proposition 12.3.1 (Perfect Recovery)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Proposition 12.3.1, (12.38), p. 372). Let `σ` be positive semi-definite and `𝒩`
a quantum channel. Every rotated Petz map recovers `σ` from `𝒩(σ)`: `ℛ^t_{σ,𝒩}(𝒩(σ)) = σ` for
every `t ∈ ℝ`.

**Formalization Note** Finite dimensions; channels in Choi–Kraus form. All powers of `σ` and
`𝒩(σ)` are taken on their supports (Definition 3.3.1). -/
theorem proposition_12_3_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix a a ℂ) (hσ : σ.PosSemidef) (N : QChannel a b) (t : ℝ) :
    rotatedPetz σ N t (N.apply σ) = σ := by sorry

end WildeQIT.Recover
