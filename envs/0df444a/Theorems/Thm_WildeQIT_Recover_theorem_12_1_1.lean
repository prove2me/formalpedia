-- Prove2me | Theorems.Thm_WildeQIT_Recover_theorem_12_1_1
-- name    : WildeQIT.Recover.theorem_12_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:21:53.396185+00:00
-- url     : https://prove2.me/theorems/ec8fece1-7b85-4f6c-9ff1-db439110ae76
-- title:
--   Theorem 12.1.1 (Recoverability) — $D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma))\ge-\log F(\rho,(\mathcal R_{\sigma,\mathcal N}\circ\mathcal N)(\rho))$
-- statement:
--   Let $\sigma$ be a positive semi-definite operator on a nonzero finite-dimensional Hilbert space $\mathcal H$ and $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ a quantum channel. There exists a quantum channel $\mathcal R_{\sigma,\mathcal N}:\mathcal L(\mathcal H')\to\mathcal L(\mathcal H)$, depending only on $\sigma$ and $\mathcal N$, such that
--
--   $$
--   (\mathcal R_{\sigma,\mathcal N}\circ\mathcal N)(\sigma)=\sigma,
--   $$
--
--   and such that for every density operator $\rho$ with $\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma)$
--
--   $$
--   D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma))\ \ge\ -\log F\!\left(\rho,(\mathcal R_{\sigma,\mathcal N}\circ\mathcal N)(\rho)\right),
--   $$
--
--   with $D$ the quantum relative entropy, $F$ the fidelity and $\log$ the binary logarithm.
--
--   Since $-\log F\ge0$, this contains the monotonicity of quantum relative entropy, and it says more: a small decrease of relative entropy means that one channel, chosen without knowledge of $\rho$, recovers $\sigma$ perfectly and $\rho$ approximately.
--
--   **Formalization Note** The recovery channel is quantified before $\rho$. Channels, both $\mathcal N$ and $\mathcal R_{\sigma,\mathcal N}$, are given in Choi–Kraus form. $-\log 0=+\infty$, and relative entropies are extended reals.
--
--   Differences from the source:
--   - reading: "Given $\rho,\sigma,\mathcal N$ … there exists a recovery channel $\mathcal R_{\sigma,\mathcal N}$, depending only on $\sigma$ and $\mathcal N$" → $\forall\sigma,\mathcal N\ \exists\mathcal R\ [\mathcal R(\mathcal N(\sigma))=\sigma\ \wedge\ \forall\rho\ (\dots)]$; reason: "depending only on $\sigma$ and $\mathcal N$" fixes the channel before $\rho$; this is the stronger reading, and the one the book proves with (12.111).
--   - encoding: quantum channels → channels in Choi–Kraus form; reason: every channel has a finite Kraus form (Theorem 4.4.1), so the existence claim is unchanged.
--   - encoding: $-\log F$ with $F=0$ → $+\infty$, and $D$ in the extended reals; reason: the book's values, represented exactly.
--   - encoding: $\rho\in\mathcal D(\mathcal H)$ given → $\mathcal H\neq0$ stated as a hypothesis; reason: the existence of a density operator already forces $\mathcal H\neq0$; with $\rho$ quantified after $\mathcal R$ it must be written out, since for $\mathcal H=0\neq\mathcal H'$ no channel $\mathcal H'\to\mathcal H$ exists.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 12.1.1, (12.1)–(12.2), p. 366; Definition 12.1.1, p. 365

import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_WildeQIT_Recover_qRelEntropy
import Definitions.Def_WildeQIT_Recover_negLog2
import Definitions.Def_WildeQIT_QChannel
open scoped ComplexOrder
open scoped ENNReal

namespace WildeQIT.Recover

/-- **Theorem 12.1.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Theorem 12.1.1, (12.1)–(12.2), p. 366). For a positive semi-definite `σ` and a quantum channel
`𝒩 : L(ℋ) → L(ℋ')` there is a recovery channel `ℛ_{σ,𝒩} : L(ℋ') → L(ℋ)`, depending only on `σ`
and `𝒩`, such that `(ℛ_{σ,𝒩} ∘ 𝒩)(σ) = σ` and, for every density operator `ρ` with
`supp(ρ) ⊆ supp(σ)`, `D(ρ‖σ) − D(𝒩(ρ)‖𝒩(σ)) ≥ −log F(ρ, (ℛ_{σ,𝒩} ∘ 𝒩)(ρ))`.

**Formalization Note** Finite dimensions; `log` is base 2. The recovery channel is quantified
before `ρ` ("depending only on `σ` and `𝒩`"). A channel is given in Choi–Kraus form, which every
channel has (Theorem 4.4.1). `−log 0 = +∞`. `ℋ` is nonzero (`Nonempty a`): Definition 12.1.1
posits `ρ ∈ 𝒟(ℋ)`, which needs `ℋ ≠ 0`; since `ρ` is quantified after `ℛ` here, this is stated
explicitly (with `ℋ = 0` and `ℋ' ≠ 0` no channel `ℋ' → ℋ` exists). -/
theorem theorem_12_1_1 {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a] [Fintype b] [DecidableEq b]
    (σ : Matrix a a ℂ) (hσ : σ.PosSemidef) (N : QChannel a b) :
    ∃ R : QChannel b a,
      R.apply (N.apply σ) = σ ∧
      ∀ ρ : Matrix a a ℂ, IsDensityOperator ρ → SuppSubset ρ σ →
        qRelEntropy ρ σ - qRelEntropy (N.apply ρ) (N.apply σ) ≥
          ((negLog2 (fidelity ρ (R.apply (N.apply ρ))) : ℝ≥0∞) : EReal) := by sorry

end WildeQIT.Recover
