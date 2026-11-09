-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_10
-- name    : SkipListConc.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:54:36.1113+00:00
-- url     : https://prove2.me/theorems/027712f1-f5ba-4459-96c0-f8978c26f955
-- title:
--   Lemma 4.10 — what the lower levels determine: $\{s_t\le\ell-1\}$, $W^+_\ell$, scan starts by $\mathcal F_\ell$; $C^+_\ell$, $C_\ell$ by $\mathcal F_{\ell+1}$
-- statement:
--   Fix $0<p<1$, an operation sequence $\sigma$ and a cutoff $L\ge1$. For every level $1\le\ell\le L$:
--
--   1. the following are determined by $\mathcal F_\ell$: for each search, whether $s_t\le\ell-1$; the count $W^+_\ell$; and the position at which each search with $s_t\le\ell-1$ starts its scan of level $\ell$;
--   2. the level costs $C^+_\ell$ and $C_\ell$ are determined by $\mathcal F_{\ell+1}$.
--
--   Here "determined by $\mathcal F_\ell$" means "a function of the list $\mathcal F_\ell$".
--
--   Differences from the source:
--   - generalization: heights following Definition 1.1 → every realization ξ of the randomness (no law assumed); reason: the statement is deterministic; the source's case is an instance
--   - encoding: "determined by F_ℓ" → ∃ g, ∀ ω, (quantity at ω) = g (F_ℓ ω); for the scan start, on the outcomes with s_t ≤ ℓ − 1; reason: the source's definition (p.18); the scan start is only defined for those searches
--   - encoding: scan position, possibly the head → WithBot α, ⊥ = head; reason: the head −∞ precedes every key
--   - encoding: A_{ℓ,t}, the left steps on level ℓ ≥ s_t of the backward walk of charge t → gapA, the levelSteps count of the time-t configuration at level ℓ (nodes y ≤ x_t of time-t height ≥ ℓ with no node of height ≥ ℓ+1 between y and x_t), charges t : Fin σ.length (0-based); reason: the same number as the walk on every level ℓ ≥ s_t, the forced first step on level s_t included and 0 above the maximum height (pp.26–27)
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.10, p.27 (backward walk, §4.5.3, pp.26–27)

import Mathlib
import Definitions.Def_SkipListConc_servedHeight
import Definitions.Def_SkipListConc_levelInfo
import Definitions.Def_SkipListConc_levelWplus
import Definitions.Def_SkipListConc_scanStart
import Definitions.Def_SkipListConc_levelC
import Definitions.Def_SkipListConc_levelCplus

namespace SkipListConc

/-- Lemma 4.10 (what the lower levels determine) (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Lemma 4.10, p.27, with the backward walk of §4.5.3, pp.26–27). For every level `1 ≤ ℓ ≤ L`:
(i) the following are determined by `F_ℓ`: for each search, whether `s_t ≤ ℓ − 1`; the count
`W⁺_ℓ`; and the position at which each search with `s_t ≤ ℓ − 1` starts its scan of level `ℓ`;
(ii) the level costs `C⁺_ℓ` and `C_ℓ` are determined by `F_{ℓ+1}`.

**Formalization Note** "Determined by `F_ℓ`" is `∃ g, ∀ ω, … = g (F_ℓ ω)`; for the scan start, on
the outcomes with `s_t ≤ ℓ − 1`. The scan start is in `WithBot α` (`⊥` = head). The statement is
pointwise in the noise, so it holds for every noise realization `ξ`. -/
theorem lemma_4_10 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (L : ℕ) (hL : 1 ≤ L) (ℓ : ℕ)
    (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    ((∀ t : Fin σ.length,
        ∃ g : ((z : σ.toFinset) → Fin (σ.count (z : α) + 1) → ℕ) → Prop,
          ∀ ω, (servedHeight p ξ σ t ω ≤ ℓ - 1 ↔ g (levelInfo p ξ σ ℓ ω))) ∧
      (∃ g : ((z : σ.toFinset) → Fin (σ.count (z : α) + 1) → ℕ) → ℕ,
          ∀ ω, levelWplus p ξ σ ℓ ω = g (levelInfo p ξ σ ℓ ω)) ∧
      (∀ t : Fin σ.length,
        ∃ g : ((z : σ.toFinset) → Fin (σ.count (z : α) + 1) → ℕ) → WithBot α,
          ∀ ω, servedHeight p ξ σ t ω ≤ ℓ - 1 →
            scanStart p ξ σ ℓ t ω = g (levelInfo p ξ σ ℓ ω))) ∧
    (∃ g : ((z : σ.toFinset) → Fin (σ.count (z : α) + 1) → ℕ) → ℕ,
        ∀ ω, levelCplus p ξ σ ℓ ω = g (levelInfo p ξ σ (ℓ + 1) ω)) ∧
    (∃ g : ((z : σ.toFinset) → Fin (σ.count (z : α) + 1) → ℕ) → ℕ,
        ∀ ω, levelC p ξ σ ℓ ω = g (levelInfo p ξ σ (ℓ + 1) ω)) := by sorry

end SkipListConc
