-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_6_10
-- name    : ReplicableDecisions.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:10:08.208047+00:00
-- url     : https://prove2.me/theorems/7e5bdd7e-6f85-41f4-9765-a155f21c8312
-- title:
--   Theorem 6.10 — local multiplicity: $n^\star\le\lceil76(\mathsf D_\rho+\log(2/\delta))/s_\rho^2\rceil$
-- statement:
--   Let $\mathcal P$ be a finite binary experiment (nonempty acceptable sets) with both forced classes $A_0,A_1$ nonempty, let $0<\beta\le1/8$, $0<\rho\le1/16$, and put $\delta=\min\{\beta,\rho/4\}$. Then
--   $$n^\star(\beta,\rho)\le n_0:=\Big\lceil\frac{76\,(\mathsf D_\rho+\log(2/\delta))}{s_\rho^2}\Big\rceil,$$
--   where $\mathsf D_\rho=\mathsf D(s_\rho/9)$ is the local packing dimension (Definition 6.7).
--
--   The bound is attained by the tournament estimate of Lemma 6.9 with $\eta=s_\rho/9$ (for every maximal $\eta$-separated net of models in any fixed order, tests run between net elements at distance at least $8\eta$), followed by the shared random odd breadth-first threshold of Theorem 3.1 on $G_{<s_\rho}$: this rule with $n_0$ samples is $(\beta,\rho)$-valid.
--
--   Since $\mathsf D_\rho\le\log M$, this never loses more than a constant factor against Theorem 3.1, and it can be much better when few models lie near each other at the chain scale.
--
--   Differences from the source:
--   - encoding: n⋆(β, ρ) = min{n : a (β, ρ)-valid n-sample algorithm exists} → the least element N of the published validSampleSizes (IsLeast); reason: a minimum read without sInf junk values; the theorem asserts it exists
--   - reading: "the tournament estimate of Lemma 6.9" with N "selected and ordered by a fixed rule" → for every maximal η-separated duplicate-free list N, the rule thresholdRule (strictGraph E s_ρ) Γ (tournament E N (8η) _) is valid; each test oriented by the order (earlier element = Q₁); reason: the page fixes no particular rule, so the claim must hold for every one; orientation only decides ties
--   - encoding: "the shared random odd breadth-first threshold of Theorem 3.1 on G_{<s_ρ}" → the published thresholdSeedLaw and thresholdRule on strictGraph E s_ρ; reason: the base mission's encoding of the same selector
--   - encoding: D_ρ = max_Q max_{j≥0} 4^{−j} log Pack(Q, 2^{j+4} s_ρ/9; s_ρ/9) → localDim E (s_ρ/9), a real supremum of a bounded family; reason: the maxima are attained, so the supremum is the maximum
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 6.10, p.34 (PDF p.36); Lemmas 6.8–6.9, pp.32–33 (PDF pp.34–35)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_weakGraph
import Definitions.Def_ReplicableDecisions_thresholdRule
import Definitions.Def_ReplicableDecisions_Supplement_localDim
import Definitions.Def_ReplicableDecisions_Supplement_tournament

namespace ReplicableDecisions.Supplement

/-- **Theorem 6.10 (Local multiplicity).** Chen, *Replicable Decisions in Finite Experiments*, STOC
2027 submission (sha256 52d181db…), Theorem 6.10, p.34 (PDF p.36). Let `P` be a finite binary
experiment with `A₀, A₁ ≠ ∅`, `0 < β ≤ 1/8`, `0 < ρ ≤ 1/16`, and `δ = min{β, ρ/4}`. Then
`n⋆(β, ρ) ≤ ⌈76(D_ρ + log(2/δ))/s_ρ²⌉`. The bound is attained by the tournament estimate of
Lemma 6.9 with `η = s_ρ/9`, followed by the shared random odd breadth-first threshold of
Theorem 3.1 on `G_{<s_ρ}`.

**Formalization Note.** `D_ρ = localDim E (s_ρ/9)`. The attainment clause is about the concrete rule
for every maximal `η`-separated net `N` and every order of it (the list `N`): Lemma 6.9's tests
between the elements of `N` at distance at least `8η`, the first element winning all its tests
(else the first element of `N`), then the published selector `thresholdRule` on `G_{<s_ρ}` with the
published seed law. The fallback model `hA₀.some` is used only if `N = []`, which maximality
excludes. -/
theorem theorem_6_10 {ι : Type*} {Z : Type} [Fintype ι] [Fintype Z] (E : Experiment ι Z)
    (Γ : ι → Set Bool) (hΓ : ∀ i, (Γ i).Nonempty) (hA₀ : (forcedClass Γ false).Nonempty)
    (hA₁ : (forcedClass Γ true).Nonempty) {β ρ : ℝ} (hβ₀ : 0 < β) (hβ : β ≤ 1 / 8) (hρ₀ : 0 < ρ)
    (hρ : ρ ≤ 1 / 16) :
    let δ : ℝ := min β (ρ / 4)
    let sρ : ℝ := hopSeparation E Γ (hopBudget ρ)
    let η : ℝ := sρ / 9
    let n₀ : ℕ := ⌈76 * (localDim E η + Real.log (2 / δ)) / sρ ^ 2⌉₊
    ∃ N : ℕ, IsLeast (validSampleSizes E Γ β ρ) N ∧ N ≤ n₀ ∧
      ∀ net : List ι, IsMaximalNet E net η →
        IsValid E Γ β ρ (thresholdSeedLaw (strictGraph E sρ) Γ)
          (thresholdRule (strictGraph E sρ) Γ
            (tournament (n := n₀) E net (8 * η) hA₀.some)) := by sorry

end ReplicableDecisions.Supplement
