-- Prove2me | Theorems.Thm_SkipListConc_lemma_3_6
-- name    : SkipListConc.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:42.778974+00:00
-- url     : https://prove2.me/theorems/04cd9315-d68b-4210-91e1-447e379732c0
-- title:
--   Lemma 3.6 — level exposure: $\mathcal F_\ell$ keeps items independent and the hazard $\ge p$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, $K\ge 1$ is an integer, and the heights follow the height-based promotion rule (Definition 1.1) with an arbitrary jump law.
--
--   Let $\sigma$ be an operation sequence, $T^\ell_y=(\min(H_y(j),\ell))_{0\le j\le f_y}$ the trajectory of item $y$ truncated at $\ell$ (with $H_y(0)=1$), and $\mathcal F_\ell=(T^\ell_y)_y$. For every level $\ell\ge1$:
--
--   1. for every item $y$, every index $0\le j\le f_y$ and every level $\ell'\le\ell$, the event $\{H_y(j)\ge\ell'\}$ is determined by $\mathcal F_\ell$;
--   2. conditional on $\mathcal F_\ell$, the height trajectories of distinct items are independent, and the conditional distribution of $y$'s trajectory depends only on $T^\ell_y$;
--   3. for every item $y$, every $1\le j_0\le f_y$, and every value $v$ of $\mathcal F_\ell$ with $\Pr[\mathcal F_\ell=v]>0$ under which $H_y(j_0)\ge\ell$,
--   $$
--   \Pr\bigl[H_y(j_0)\ge\ell+1\ \big|\ \mathcal F_\ell=v\bigr]\ \ge\ p .
--   $$
--
--   Part 3 is property (T3) with the conditioning on all items at once; it is what lets the levels of the horizontal cost be combined without a union bound.
--
--   Differences from the source:
--   - encoding: Definition 1.1: gate with probability p^c, jump J_c ∈ {1,…,K} with a law depending only on c, G ∼ Geom₀(1−p), all fresh and independent across updates and items → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); gate U ≤ p^c; jump J c + 1; reason: realizes exactly the transition probabilities (1) and the independence of Definition 1.1; μJ is an arbitrary jump law
--   - encoding: "determined by F_ℓ" → ∃ g, ∀ ω, (quantity at ω) = g (F_ℓ ω); reason: the source's definition: a function of the list F_ℓ (p.18)
--   - encoding: conditional on F_ℓ → conditioning on an atom {F_ℓ = v} of positive probability (ProbabilityTheory.cond); reason: the source's convention: F_ℓ is finitely valued and only positive-probability values are used (p.18)
--   - reading: "the conditional distribution of y's trajectory depends only on T^ℓ_y" → the law of y's trajectory given {F_ℓ = v} equals its law given {T^ℓ_y = v_y}; reason: the proof's statement of it (p.19): y's trajectory has the distribution it has given {T^ℓ_y = v_y} alone
--   - encoding: "under which H_y(j₀) ≥ ℓ" → v_y(j₀) = ℓ; reason: a height is ≥ ℓ exactly when its truncation at ℓ equals ℓ
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 3.6, p.18 (level filtration, §3.3, p.18)

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_traj
import Definitions.Def_SkipListConc_truncTraj
import Definitions.Def_SkipListConc_levelInfo

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 3.6 (level exposure along trajectories) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 3.6, p.18, with the level filtration of §3.3, p.18). For every level `ℓ ≥ 1`:
(i) for every item `y`, every index `0 ≤ j ≤ f_y` and every level `ℓ' ≤ ℓ`, the event
`{H_y(j) ≥ ℓ'}` is determined by `F_ℓ`;
(ii) conditional on `F_ℓ`, the height trajectories of distinct items are independent, and the
conditional distribution of `y`'s trajectory depends only on `T^ℓ_y`;
(iii) for every item `y`, every `1 ≤ j₀ ≤ f_y`, and every value `v` of `F_ℓ` with
`Pr[F_ℓ = v] > 0` under which `H_y(j₀) ≥ ℓ`, `Pr[H_y(j₀) ≥ ℓ + 1 | F_ℓ = v] ≥ p`.

**Formalization Note** "Determined by `F_ℓ`" is "a function of the list `F_ℓ`" (p.18), i.e.
`∃ g, ∀ ω, … = g (F_ℓ ω)`. Conditioning on `F_ℓ` is conditioning on an atom `{F_ℓ = v}` of
positive probability. In (ii), "depends only on `T^ℓ_y`" is: the law of `y`'s trajectory given
`{F_ℓ = v}` equals its law given `{T^ℓ_y = v_y}`. "`H_y(j₀) ≥ ℓ` under `v`" is `v_y(j₀) = ℓ`.
Trajectories are indexed by `j = 0, …, f_y` with `H_y(0) = 1`. -/
theorem lemma_3_6 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α Ω : Type*} [DecidableEq α] [MeasurableSpace Ω] (P : Measure Ω)
    (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ)
    (hξ : IsPromotionNoise p K μJ P ξ) (σ : List α) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ (y : σ.toFinset) (j : Fin (σ.count (y : α) + 1)) (ℓ' : ℕ), ℓ' ≤ ℓ →
        ∃ g : ((z : σ.toFinset) → Fin (σ.count (z : α) + 1) → ℕ) → Prop,
          ∀ ω, (ℓ' ≤ height p ξ (y : α) j ω ↔ g (levelInfo p ξ σ ℓ ω))) ∧
      (∀ v : (z : σ.toFinset) → Fin (σ.count (z : α) + 1) → ℕ,
        P (levelInfo p ξ σ ℓ ⁻¹' {v}) ≠ 0 →
          iIndepFun (fun y : σ.toFinset => traj p ξ σ y)
              (ProbabilityTheory.cond P (levelInfo p ξ σ ℓ ⁻¹' {v})) ∧
            ∀ y : σ.toFinset,
              (ProbabilityTheory.cond P (levelInfo p ξ σ ℓ ⁻¹' {v})).map (traj p ξ σ y) =
                (ProbabilityTheory.cond P (truncTraj p ξ σ ℓ y ⁻¹' {v y})).map
                  (traj p ξ σ y)) ∧
      ∀ (y : σ.toFinset) (j₀ : Fin (σ.count (y : α) + 1)), 1 ≤ (j₀ : ℕ) →
        ∀ v : (z : σ.toFinset) → Fin (σ.count (z : α) + 1) → ℕ,
          P (levelInfo p ξ σ ℓ ⁻¹' {v}) ≠ 0 → v y j₀ = ℓ →
            ENNReal.ofReal p ≤
              ProbabilityTheory.cond P (levelInfo p ξ σ ℓ ⁻¹' {v})
                {ω | ℓ + 1 ≤ height p ξ (y : α) j₀ ω} := by sorry

end SkipListConc
