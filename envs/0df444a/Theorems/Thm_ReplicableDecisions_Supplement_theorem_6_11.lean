-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_6_11
-- name    : ReplicableDecisions.Supplement.theorem_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:11:02.955951+00:00
-- url     : https://prove2.me/theorems/565aaaf0-5381-4aa8-adfc-c0cf7d069fa7
-- title:
--   Theorem 6.11 — robustness at the chain scale: $n^\star\le n^\star_{\mathcal T_\tau}\le\lceil240\,s^{-2}\log(M/\delta)\rceil$
-- statement:
--   Under the assumptions of Theorem 3.1 (a finite binary experiment with nonempty acceptable sets, both forced classes nonempty, $0<\beta\le1/8$, $0<\rho\le1/16$), put $s=s_\rho$ and $\delta=\min\{\beta,\rho/4\}$. There is an absolute constant $C>0$ such that for every $0\le\tau\le s/16$:
--   1. every $\Gamma_\tau(Q)$, $Q\in\mathcal T_\tau$, is nonempty;
--   2. $\displaystyle n^\star(\beta,\rho)\le n^\star_{\mathcal T_\tau}(\beta,\rho)\le n_1:=\Big\lceil\frac{240}{s^2}\log\frac M\delta\Big\rceil$;
--   3. the upper bound is attained by robust pairwise tests (Lemma 6.8) between all pairs of models at distance at least $s/2$ on the same sample, taking the first model (in any fixed order) that wins all its comparisons, else the first model, followed by the graph selector of Theorem 3.1 on $G_{<s}$: this rule with $n_1$ samples is robustly $(\beta,\rho)$-valid on $\mathcal T_\tau$;
--   4. $n_1\le C\log(M/\delta)\,n^\star(\beta,\rho)$, i.e. the sample size is $O(\log(M/\delta))$ times the optimum for the original experiment.
--
--   So agreement and accuracy can be guaranteed on a Hellinger neighborhood of the family whose radius is proportional to the chain scale.
--
--   Differences from the source:
--   - encoding: n⋆(β, ρ) = min{n : a (β, ρ)-valid n-sample algorithm exists} → the least element N of the published validSampleSizes (IsLeast); reason: a minimum read without sInf junk values; the theorem asserts it exists
--   - encoding: n⋆_{T_τ} and T_τ = {Q on Z : min_P h(Q, P) ≤ τ} → least element of robustValidSampleSizes; Q ∈ stdSimplex ℝ Z with some model within τ; reason: the page's definitions (p.34) in the Lean model
--   - reading: "The upper bound uses robust pairwise tests on the finite family, followed by the graph selector of Theorem 3.1" → the rule of the proof (p.35) for every duplicate-free list of all models (the fixed order), via tournament with θ = s/2 and the published thresholdRule on strictGraph E s; reason: the proof fixes no particular order, so the claim must hold for every one
--   - encoding: "Its sample size is O(log(M/δ)) times the optimum" → one absolute C > 0, quantified before the experiment and all parameters, with n₁ ≤ C log(M/δ) N; reason: the Lean reading of O(·) with an absolute constant
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 6.11, (6.12), p.34 (PDF p.36); proof, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_weakGraph
import Definitions.Def_ReplicableDecisions_thresholdRule
import Definitions.Def_ReplicableDecisions_Supplement_tournament
import Definitions.Def_ReplicableDecisions_Supplement_robustValidSampleSizes

namespace ReplicableDecisions.Supplement

/-- **Theorem 6.11 (Robustness at the chain scale).** Chen, *Replicable Decisions in Finite
Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 6.11, (6.12), p.34 (PDF p.36). Under
the assumptions of Theorem 3.1, put `s = s_ρ` and `δ = min{β, ρ/4}`. For every `0 ≤ τ ≤ s/16`, all
sets `Γ_τ(Q)` are nonempty and `n⋆(β, ρ) ≤ n⋆_{T_τ}(β, ρ) ≤ ⌈(240/s²) log(M/δ)⌉`. The upper bound
uses robust pairwise tests on the finite family, followed by the graph selector of Theorem 3.1. Its
sample size is `O(log(M/δ))` times the optimum for the original experiment.

**Formalization Note.** `N` is `n⋆`, `Nτ` is `n⋆_{T_τ}` (both `IsLeast`). The rule is the proof's
(p.35): every pair of models at distance at least `s/2` is tested by Lemma 6.8 on the same sample,
`P̂` is the first model in the order that wins all its comparisons (else the first model), and the
published selector `thresholdRule` on `G_{<s}` is applied; the clause holds for every order of the
models. The `O(log(M/δ))` clause has one absolute constant `C`, quantified before everything. -/
theorem theorem_6_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type*} {Z : Type} [Fintype ι] [Fintype Z] (E : Experiment ι Z) (Γ : ι → Set Bool),
        (∀ i, (Γ i).Nonempty) → ∀ (hA₀ : (forcedClass Γ false).Nonempty),
        (forcedClass Γ true).Nonempty →
        ∀ β ρ : ℝ, 0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
        let δ : ℝ := min β (ρ / 4)
        let M : ℝ := Fintype.card ι
        let s : ℝ := hopSeparation E Γ (hopBudget ρ)
        let n₁ : ℕ := ⌈240 / s ^ 2 * Real.log (M / δ)⌉₊
        ∀ τ : ℝ, 0 ≤ τ → τ ≤ s / 16 →
          (∀ q ∈ robustNbhd E τ, (robustΓ E Γ τ q).Nonempty) ∧
          ∃ N Nτ : ℕ, IsLeast (validSampleSizes E Γ β ρ) N ∧
            IsLeast (robustValidSampleSizes E Γ τ β ρ) Nτ ∧ N ≤ Nτ ∧ Nτ ≤ n₁ ∧
            (∀ order : List ι, order.Nodup → (∀ i, i ∈ order) →
              IsRobustValid E Γ τ β ρ (thresholdSeedLaw (strictGraph E s) Γ)
                (thresholdRule (strictGraph E s) Γ
                  (tournament (n := n₁) E order (s / 2) hA₀.some))) ∧
            (n₁ : ℝ) ≤ C * Real.log (M / δ) * N := by sorry

end ReplicableDecisions.Supplement
