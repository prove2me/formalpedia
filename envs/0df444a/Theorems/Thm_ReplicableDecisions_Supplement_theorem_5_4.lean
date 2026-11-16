-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_5_4
-- name    : ReplicableDecisions.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:07:13.765598+00:00
-- url     : https://prove2.me/theorems/fb5af8bf-f8c8-4ec8-9309-d20db84cb938
-- title:
--   Theorem 5.4 — confidence and chain geometry need not separate
-- statement:
--   For every integer $m\ge5$ there is a finite binary experiment with $M=4m(m-4)+3$ Bernoulli models (nonempty acceptable sets, both forced classes nonempty) such that, for $\rho_m=m^{-2}$ and $\beta_m=e^{-m^2}$,
--   $$s_1^2=1-\frac{\sqrt3}2,\qquad \frac1{3m^2}\le s_{\rho_m}^2\le\frac1{m^2},$$
--   and
--   $$\frac{m^4}{100}<n^\star(\beta_m,\rho_m)\le\Big\lceil3m^2\big[m^2+\log(4m^2)\big]\Big\rceil\le6m^4+1.$$
--
--   Consequently there is no constant $C$ such that
--   $$n^\star(\beta,\rho)\le C\Big[s_\rho^{-2}\log\frac M\rho+s_1^{-2}\log\frac1\beta\Big]$$
--   holds for every finite binary experiment with nonempty acceptable sets and both forced classes nonempty, and every $0<\beta\le1/8$, $0<\rho\le1/16$.
--
--   So the product $s_\rho^{-2}\log(1/\beta)$ in the general upper bound can have the correct order, even though $s_1$ stays bounded away from zero.
--
--   Differences from the source:
--   - encoding: M Bernoulli models → an experiment on the observation space Bool, index type ι : Type of cardinality 4m(m − 4) + 3; reason: every law on {0, 1} is a Bernoulli law
--   - reading: "a finite binary experiment" → also asserts (∀ i, Γ i nonempty) and both forced classes nonempty; reason: the §2 standing assumptions of a binary experiment; s₁ and s_ρ are defined only with both forced classes nonempty, and the proof's P₋, P₊ are the forced models
--   - encoding: n⋆(β, ρ) = min{n : a (β, ρ)-valid n-sample algorithm exists} → the least element N of the published validSampleSizes (IsLeast); reason: a minimum read without sInf junk values; the theorem asserts it exists
--   - encoding: "no universal constant C can make (5.5) hold for every finite binary experiment in the parameter range of Theorem 3.1" → ¬ ∃ C : ℝ, ∀ ι Z : Type finite, every experiment with nonempty acceptable sets and both forced classes nonempty, ∀ 0 < β ≤ 1/8, 0 < ρ ≤ 1/16, ∀ N with IsLeast (validSampleSizes) N, N ≤ C[…]; reason: n⋆ exists in that range (Theorem 3.1), so "n⋆ ≤ X" is "every least element is ≤ X"
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 5.4, (5.3)–(5.5), p.24 (PDF p.26)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation

namespace ReplicableDecisions.Supplement

/-- **Theorem 5.4 (Confidence and chain geometry need not separate).** Chen, *Replicable Decisions
in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 5.4, (5.3)–(5.5), p.24
(PDF p.26). For every integer `m ≥ 5` there is a finite binary experiment with
`M = 4m(m − 4) + 3` Bernoulli models such that, for `ρ_m = m⁻²` and `β_m = e^{−m²}`,
`s₁² = 1 − √3/2`, `1/(3m²) ≤ s²_{ρ_m} ≤ 1/m²`, and
`m⁴/100 < n⋆(β_m, ρ_m) ≤ ⌈3m²[m² + log(4m²)]⌉ ≤ 6m⁴ + 1`. Consequently no universal constant `C`
makes `n⋆(β, ρ) ≤ C[s_ρ⁻² log(M/ρ) + s₁⁻² log(1/β)]` hold for every finite binary experiment in the
parameter range of Theorem 3.1.

**Formalization Note.** The observation space is `Bool`, so every model is a Bernoulli law. The
constructed experiment is also asserted to have nonempty acceptable sets and both forced classes
nonempty. In the second part, `n⋆` is any least element (`IsLeast`); it exists in that range by
Theorem 3.1. -/
theorem theorem_5_4 :
    (∀ m : ℕ, 5 ≤ m →
      ∃ (ι : Type) (_ : Fintype ι) (E : Experiment ι Bool) (Γ : ι → Set Bool),
        Fintype.card ι = 4 * m * (m - 4) + 3 ∧ (∀ i, (Γ i).Nonempty) ∧
        (forcedClass Γ false).Nonempty ∧ (forcedClass Γ true).Nonempty ∧
        hopSeparation E Γ 1 ^ 2 = 1 - Real.sqrt 3 / 2 ∧
        1 / (3 * (m : ℝ) ^ 2) ≤ hopSeparation E Γ (hopBudget (1 / (m : ℝ) ^ 2)) ^ 2 ∧
        hopSeparation E Γ (hopBudget (1 / (m : ℝ) ^ 2)) ^ 2 ≤ 1 / (m : ℝ) ^ 2 ∧
        ∃ N : ℕ, IsLeast (validSampleSizes E Γ (Real.exp (-(m : ℝ) ^ 2)) (1 / (m : ℝ) ^ 2)) N ∧
          (m : ℝ) ^ 4 / 100 < (N : ℝ) ∧
          N ≤ ⌈3 * (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 + Real.log (4 * (m : ℝ) ^ 2))⌉₊ ∧
          (⌈3 * (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 + Real.log (4 * (m : ℝ) ^ 2))⌉₊ : ℝ) ≤
            6 * (m : ℝ) ^ 4 + 1) ∧
    ¬ ∃ C : ℝ, ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (E : Experiment ι Z) (Γ : ι → Set Bool),
      (∀ i, (Γ i).Nonempty) → (forcedClass Γ false).Nonempty → (forcedClass Γ true).Nonempty →
      ∀ β ρ : ℝ, 0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
      ∀ N : ℕ, IsLeast (validSampleSizes E Γ β ρ) N →
        (N : ℝ) ≤ C * (1 / hopSeparation E Γ (hopBudget ρ) ^ 2 *
            Real.log ((Fintype.card ι : ℝ) / ρ) +
          1 / hopSeparation E Γ 1 ^ 2 * Real.log (1 / β)) := by sorry

end ReplicableDecisions.Supplement
