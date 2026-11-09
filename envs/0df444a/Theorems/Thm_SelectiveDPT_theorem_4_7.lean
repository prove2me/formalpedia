-- Prove2me | Theorems.Thm_SelectiveDPT_theorem_4_7
-- name    : SelectiveDPT.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:09.956385+00:00
-- url     : https://prove2.me/theorems/805daac4-ac67-4b0a-a364-d97ed13fcb1d
-- title:
--   Theorem 4.7 — the relational multiplicative adversary satisfies a strong selective direct product property
-- statement:
--   Let $0 < \delta \le 1/8$ and $\lambda > 1$. There are an integer $k_0 = k_0(\lambda,\delta) \ge 1$ and a number $\kappa = \kappa(\lambda,\delta)$ with $0 < \kappa < 1$ such that the following holds. Let $\eta > 0$ with $\eta \le 2^{-H_2(\delta)/(7/8-\delta)}$ and let $\varepsilon$ satisfy $1/2 - \eta - \sqrt{2\eta} \le \varepsilon < 1-\eta$. Let $R \subseteq D \times Y$ be a relation on $D \subseteq X^n$ and $\mathcal D$ a distribution on $D$. Then for all integers $m \ge k \ge k_0$,
--   $$Q^{\mathcal D^m}_{1-\kappa^k}\big(R^{(k,m)}\big) \;\ge\; \delta k \cdot \mathrm{MADV}^{\mathcal D}_{\varepsilon,\lambda,\eta}(R).$$
--
--   Here $Q^{\mathcal D^m}$ is the distributional complexity under the product distribution of $m$ independent copies, $R^{(k,m)}$ is the selective direct product and $H_2$ the binary entropy in bits. This is the precise form of the informal Theorem 1.8.
--
--   Differences from the source:
--   - reading: there is a k₀ = k₀(λ, δ) ≥ 1 … for some κ = κ(λ, δ) < 1 → ∃ k₀ ≥ 1 and κ < 1 chosen after δ and λ and before η, ε, d, n, Y, D, R, μ, m, k; reason: the notation k₀(λ, δ), κ(λ, δ) says they depend only on λ and δ
--   - generalization: κ < 1 → 0 < κ < 1; reason: the proof's κ = κ(k₀) is positive; a positive κ is needed to write κ = (1 − ε)^γ in Theorem 4.9
--   - encoding: m-copy inputs in (X^n)^m, outputs ((i_1, y_1), …, (i_k, y_k)) with i_1 ≠ ⋯ ≠ i_k → inputs on Fin m × Fin n (copy, position), outputs Fin k → Fin m × Y with injective copy indices; reason: footnote 5 (p.9) indexes queries by (copy, position); an ordered injective tuple is a k-set of copies with labels (p.10)
--   - encoding: inputs x ∈ X^n with |X| = d, a T-query algorithm measuring its work register and post-processing the result → X = ZMod d, inputs Fin n → ZMod d with a Finset domain D, QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map, query complexity in ℕ∞ (⊤ if no algorithm exists) compared in [0, ∞]; reason: relabelling X as Z_d is the paper's own convention (p.9); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 4.7, p.33; proof pp.34–37

import Mathlib
import Definitions.Def_SelectiveDPT_Qdist
import Definitions.Def_SelectiveDPT_madv
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_selRel
import Definitions.Def_SelectiveDPT_H2

open scoped ENNReal

universe u

namespace SelectiveDPT

/-- Theorem 4.7 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.33: let `R ⊆ D × Y` for
`D ⊆ X^n` be a relation and `D` a distribution over `D`. Let `0 < δ ≤ 1/8`, `λ > 1` and `η > 0`
satisfy `η ≤ 2^{−H₂(δ)/(7/8−δ)}`, where `H₂` is the binary entropy function. For
`1/2 − η − √(2η) ≤ ε < 1 − η`, there is a `k₀ = k₀(λ, δ) ≥ 1` such that for any integers
`m ≥ k ≥ k₀`, `Q^{D^m}_{1−κ^k}(R^(k,m)) ≥ δk · MADV^D_{ε,λ,η}(R)` for some `κ = κ(λ, δ) < 1`.

**Formalization Note.** `k₀` and `κ` are chosen after `δ` and `λ` only and before `η`, `ε`, the
relation, the distribution and `m, k` (the paper's `k₀(λ, δ)` and `κ(λ, δ)`). `0 < κ` is added.
`H₂` is in bits. The left side is the distributional complexity of `R^(k,m)` on `D^m` under the
product distribution `μ^m`, with inputs indexed by `Fin m × Fin n` (one query reads one position of
one copy); the right side uses the single-copy `MADV` under `μ`. -/
theorem theorem_4_7 (δ lam : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1 / 8) (hlam : 1 < lam) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧
      ∀ η ε : ℝ, 0 < η → η ≤ (2 : ℝ) ^ (-H2 δ / (7 / 8 - δ)) →
        1 / 2 - η - Real.sqrt (2 * η) ≤ ε → ε < 1 - η →
        ∀ (d n : ℕ) [NeZero d] (Y : Type u) (D : Finset (Fin n → ZMod d))
          (R : (Fin n → ZMod d) → Y → Prop) (μ : (Fin n → ZMod d) → ℝ), IsDistOn μ D →
          ∀ m k : ℕ, k₀ ≤ k → k ≤ m →
            ENNReal.ofReal (δ * k) * madv μ D R ε lam η ≤
              (Qdist (prodDomain D m) (prodDist μ m) (selRel k m R) (1 - κ ^ k) : ℝ≥0∞) := by sorry

end SelectiveDPT
