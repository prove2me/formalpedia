-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_4_5
-- name    : ReplicableDecisions.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:06:33.319223+00:00
-- url     : https://prove2.me/theorems/a312a872-9d04-48cf-8b3d-50e76ee41ef0
-- title:
--   Theorem 4.5 — ordered product experiments: additive confidence cost, $n^\star=\Theta_A(\lambda^{-1}\log(1+\frac1{d\rho})+\frac1{d\lambda}\log\frac1\beta)$
-- statement:
--   Let $Q_i^-\ne Q_i^+$ ($1\le i\le d$, $d\ge1$) be strictly positive laws on finite alphabets $\mathcal Z_i$, let $P_j=\bigotimes_{i\le j}Q_i^+\otimes\bigotimes_{i>j}Q_i^-$ ($j=0,\dots,d$) carry the early/late acceptable sets of (4.1), and write $\lambda_i=-\log\mathrm{BC}(Q_i^-,Q_i^+)$.
--
--   For every constant $A\ge1$ there are constants $C_1,C_2,C_3,C_4>0$, depending only on $A$, such that the following holds whenever, for some $\lambda>0$,
--   $$\lambda\le\lambda_i\le A\lambda,\qquad \mathrm{KL}(Q_i^-\|Q_i^+)\le A\lambda\quad(1\le i\le d),\qquad d\lambda\le1.$$
--   1. For the original forced classes, $C_3\,d\lambda\le s_1^2\le C_4\,d\lambda$.
--   2. For $0<\beta\le1/8$ and $0<\rho\le1/16$,
--   $$C_1F\le n^\star(\beta,\rho)\le C_2F,\qquad F=\frac1\lambda\log\Big(1+\frac1{d\rho}\Big)+\frac1{d\lambda}\log\frac1\beta.$$
--   3. If $\hat\jmath$ is a maximum-likelihood position (any fixed tie-breaking) and $U\sim\mathrm{Unif}[d/3,2d/3]$ is shared, the output $\mathbf 1\{\hat\jmath\ge U\}$ is $(\beta,\rho)$-valid with
--   $$n=\Big\lceil\max\Big\{\frac1\lambda\log\Big(1+\frac{12}{d\rho}\Big),\ \frac{12}{d\lambda}\log\frac1\beta\Big\}\Big\rceil$$
--   samples.
--
--   The confidence term is thus charged at the original forced-pair scale, independently of the replication term.
--
--   Differences from the source:
--   - encoding: Θ_A with "constants depend only on A" → ∀ A ≥ 1, ∃ C₁ C₂ C₃ C₄ > 0 quantified before d, the alphabets, the laws, λ, β and ρ; reason: the Lean reading of Θ_A
--   - encoding: n⋆(β, ρ) = min{n : a (β, ρ)-valid n-sample algorithm exists} → the least element N of the published validSampleSizes (IsLeast); reason: a minimum read without sInf junk values; the theorem asserts it exists
--   - encoding: the standing d ≥ 1 of (4.1) ("the early/late acceptable sets of (4.1)") → hypothesis 1 ≤ d; reason: (4.1) fixes d ≥ 1; d = 0 makes 1/(dλ) undefined and both forced ranges contain j = 0
--   - encoding: heterogeneous finite alphabets Z_i, product representation → Zs : Fin d → Type with Fintype, observations (i : Fin d) → Zs i, blocks 0-based; reason: Lean indexing; the same family
--   - encoding: ĵ a maximum-likelihood position with fixed tie breaking; U ∼ Unif[d/3, 2d/3] → every jhat with IsMaxLikelihood (P_jⁿ(x) ≤ P_{ĵ(x)}ⁿ(x) for all j, x); seed space ℝ with Lebesgue measure conditioned on [d/3, 2d/3]; output decide (U ≤ ĵ); reason: every fixed tie-break is such a selection; the uniform law is that conditional measure
--   - encoding: KL(Q⁻_i ∥ Q⁺_i), BC → klDiv = ∑ P log(P/Q) (natural log); BC = the published FuchsVdGraaf.bhattacharyya; reason: textbook formulas on strictly positive laws
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 4.5, (4.18)–(4.20), pp.21–22 (PDF pp.23–24)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_IsMaxLikelihood
import Definitions.Def_ReplicableDecisions_Supplement_orderedProductExperiment
import Definitions.Def_ReplicableDecisions_Supplement_klDiv
import Definitions.Def_ReplicableDecisions_Supplement_positionRule

open MeasureTheory

namespace ReplicableDecisions.Supplement

/-- **Theorem 4.5 (A structural class with additive confidence cost).** Chen, *Replicable Decisions
in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 4.5, (4.18)–(4.20),
pp.21–22 (PDF pp.23–24). Fix `A ≥ 1`. For the ordered product family of distinct strictly positive
laws `Q⁻_i, Q⁺_i` with the acceptable sets of (4.1), suppose that for some `λ > 0`,
`λ ≤ λ_i ≤ Aλ`, `KL(Q⁻_i ∥ Q⁺_i) ≤ Aλ` (`1 ≤ i ≤ d`) and `dλ ≤ 1`. For `0 < β ≤ 1/8` and
`0 < ρ ≤ 1/16`, `n⋆(β, ρ) = Θ_A((1/λ) log(1 + 1/(dρ)) + (1/(dλ)) log(1/β))`, the constants depending
only on `A`. If `ĵ` is a maximum-likelihood position with fixed tie breaking and
`U ∼ Unif[d/3, 2d/3]` is shared, `1{ĵ ≥ U}` is valid for
`n = ⌈max{(1/λ) log(1 + 12/(dρ)), (12/(dλ)) log(1/β)}⌉`. For the original forced classes,
`s₁² = Θ_A(dλ)`.

**Formalization Note.** `λ` is written `lam`; `λ_i` is `blockExponent`. The four constants are
quantified after `A` and before every other parameter. `d ≥ 1` is the standing assumption of (4.1).
Every likelihood maximizer `ĵ` (every fixed tie-break) is covered. -/
theorem theorem_4_5 :
    ∀ A : ℝ, 1 ≤ A → ∃ C₁ C₂ C₃ C₄ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < C₄ ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (Zs : Fin d → Type) [∀ i, Fintype (Zs i)]
        (Qm Qp : (i : Fin d) → Zs i → ℝ) (hm : ∀ i, Qm i ∈ stdSimplex ℝ (Zs i))
        (hp : ∀ i, Qp i ∈ stdSimplex ℝ (Zs i)) (hposm : ∀ i z, 0 < Qm i z),
        (∀ i z, 0 < Qp i z) → ∀ (hne : ∀ i, Qm i ≠ Qp i) (lam : ℝ), 0 < lam →
        (∀ i, lam ≤ blockExponent Qm Qp i ∧ blockExponent Qm Qp i ≤ A * lam ∧
          klDiv (Qm i) (Qp i) ≤ A * lam) →
        (d : ℝ) * lam ≤ 1 →
        let E := orderedProductExperiment Qm Qp hm hp hposm hne
        let s₁ : ℝ := hopSeparation E (earlyLateΓ d) 1
        (C₃ * ((d : ℝ) * lam) ≤ s₁ ^ 2 ∧ s₁ ^ 2 ≤ C₄ * ((d : ℝ) * lam)) ∧
        ∀ β ρ : ℝ, 0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
          let F : ℝ := 1 / lam * Real.log (1 + 1 / ((d : ℝ) * ρ)) +
            1 / ((d : ℝ) * lam) * Real.log (1 / β)
          let n₀ : ℕ := ⌈max (1 / lam * Real.log (1 + 12 / ((d : ℝ) * ρ)))
            (12 / ((d : ℝ) * lam) * Real.log (1 / β))⌉₊
          (∃ N : ℕ, IsLeast (validSampleSizes E (earlyLateΓ d) β ρ) N ∧
            C₁ * F ≤ (N : ℝ) ∧ (N : ℝ) ≤ C₂ * F) ∧
          ∀ jhat : (Fin n₀ → ((i : Fin d) → Zs i)) → Fin (d + 1), IsMaxLikelihood E jhat →
            IsValid E (earlyLateΓ d) β ρ (positionSeedLaw d) (positionRule jhat) := by sorry

end ReplicableDecisions.Supplement
