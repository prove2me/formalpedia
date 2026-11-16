-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_6_12
-- name    : ReplicableDecisions.Supplement.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:11:36.446204+00:00
-- url     : https://prove2.me/theorems/d74d1dd9-1daf-4979-b713-5839445b5d94
-- title:
--   Theorem 6.12 — compression with a common reverse channel
-- statement:
--   Let $\mathcal E=(\mathcal P,\Gamma)$ be a finite binary experiment on $\mathcal Z$ (nonempty acceptable sets), $K$ an admissible channel from $\mathcal Z$ to a finite $\mathcal W$, and $\mathcal E_K=(\mathcal Q,\Gamma_K)$ the compressed experiment. Suppose there is a channel $J$ from $\mathcal W$ to $\mathcal Z$ such that, for every $Q\in\mathcal Q$,
--   $$P_Q:=QJ\in\mathcal P,\qquad P_QK=Q,\qquad \Gamma(P_Q)=\Gamma_K(Q).$$
--   Then:
--   1. for every $0\le\beta,\rho\le1$, the sample sizes admitting a $(\beta,\rho)$-valid algorithm are the same for $\mathcal E$ and $\mathcal E_K$; in particular $n^\star_{\mathcal E}(\beta,\rho)=n^\star_{\mathcal E_K}(\beta,\rho)$, including when both are $+\infty$;
--   2. if both forced classes of $\mathcal E$ are nonempty, $s_L(\mathcal E)=s_L(\mathcal E_K)$ for every integer $L\ge1$;
--   3. consequently, if both forced classes are nonempty, $0<\beta\le1/8$, $0<\rho\le1/16$, $\delta=\min\{\beta,\rho/4\}$ and $M_K=|\mathcal Q|$,
--   $$\frac1{4608\,s_\rho(\mathcal E)^2}<n^\star_{\mathcal E}(\beta,\rho)\le\Big\lceil\frac{\log(M_K/\delta)}{s_\rho(\mathcal E)^2}\Big\rceil.$$
--
--   The raw model count in Theorem 3.1 can thus be replaced by the compressed count without changing the optimal sample size or any chain scale.
--
--   Differences from the source:
--   - generalization: n⋆_E(β, ρ) = n⋆_{E_K}(β, ρ) for every 0 ≤ β, ρ ≤ 1 → validSampleSizes E Γ β ρ = validSampleSizes E_K Γ_K β ρ; reason: the proof states "This proves equality of feasible sample sizes, including n = 0" (p.36); equal sets have equal minima, including min ∅ = +∞, so this specializes to the printed claim
--   - encoding: E_K = (Q, Γ_K), M_K = |Q| → compressedExperiment indexed by the image set channelImage E K; M_K its cardinality; reason: the models of E_K are the distinct image laws
--   - encoding: (6.13): P_Q := QJ ∈ P, P_Q K = Q, Γ(P_Q) = Γ_K(Q) → ∀ q, ∃ i, E.P i = qJ ∧ (E.P i)K = q ∧ Γ i = Γ_K q; reason: membership in P is "equal to some model"; models are distinct, so Γ(P_Q) is Γ at that index
--   - encoding: n⋆(β, ρ) = min{n : a (β, ρ)-valid n-sample algorithm exists} → the least element N of the published validSampleSizes (IsLeast); reason: a minimum read without sInf junk values; the theorem asserts it exists
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 6.12, (6.13)–(6.14), p.36 (PDF p.38); §6.4, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_Supplement_compressedExperiment

namespace ReplicableDecisions.Supplement

/-- **Theorem 6.12 (Compression with a common reverse channel).** Chen, *Replicable Decisions in
Finite Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 6.12, (6.13)–(6.14), p.36
(PDF p.38). Let `E = (P, Γ)` be a finite binary experiment on `Z`, `K` an admissible channel from
`Z` to a finite `W`, and `E_K = (Q, Γ_K)` the compressed experiment. Suppose there is a channel `J`
from `W` to `Z` such that, for every `Q ∈ Q`, `P_Q := QJ ∈ P`, `P_Q K = Q` and
`Γ(P_Q) = Γ_K(Q)`. Then `n⋆_E(β, ρ) = n⋆_{E_K}(β, ρ)` for every `0 ≤ β, ρ ≤ 1`. If both forced
classes of `E` are nonempty, then `s_L(E) = s_L(E_K)` for every `L ≥ 1`, and in the parameter range
of Theorem 3.1, with `δ = min{β, ρ/4}` and `M_K = |Q|`,
`1/(4608 s_ρ(E)²) < n⋆_E(β, ρ) ≤ ⌈log(M_K/δ)/s_ρ(E)²⌉`.

**Formalization Note.** `E_K` is indexed by the image set `Q` (`channelImage E K`), so
`M_K = |Q|` is its number of models. The first clause is stated as equality of the sets of feasible
sample sizes, which gives equality of the minima including the case `min ∅ = +∞`. -/
theorem theorem_6_12 {ι : Type*} {Z W : Type} [Fintype ι] [Fintype Z] [Fintype W]
    (E : Experiment ι Z) (Γ : ι → Set Bool) (hΓ : ∀ i, (Γ i).Nonempty) (K : Z → W → ℝ)
    (hK : IsChannel K) (hadm : IsAdmissible E K Γ) (J : W → Z → ℝ) (hJ : IsChannel J)
    (h613 : ∀ q : channelImage E K, ∃ i, E.P i = pushforward q.1 J ∧
      pushforward (E.P i) K = q.1 ∧ Γ i = compressedΓ E K Γ q) :
    let EK := compressedExperiment E K hK
    let ΓK := compressedΓ E K Γ
    (∀ β ρ : ℝ, 0 ≤ β → β ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      validSampleSizes E Γ β ρ = validSampleSizes EK ΓK β ρ) ∧
    ((forcedClass Γ false).Nonempty → (forcedClass Γ true).Nonempty →
      ∀ L : ℕ, 1 ≤ L → hopSeparation E Γ L = hopSeparation EK ΓK L) ∧
    ((forcedClass Γ false).Nonempty → (forcedClass Γ true).Nonempty →
      ∀ β ρ : ℝ, 0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
        let δ : ℝ := min β (ρ / 4)
        let sρ : ℝ := hopSeparation E Γ (hopBudget ρ)
        ∃ N : ℕ, IsLeast (validSampleSizes E Γ β ρ) N ∧ 1 / (4608 * sρ ^ 2) < (N : ℝ) ∧
          N ≤ ⌈Real.log ((Fintype.card (channelImage E K) : ℝ) / δ) / sρ ^ 2⌉₊) := by sorry

end ReplicableDecisions.Supplement
