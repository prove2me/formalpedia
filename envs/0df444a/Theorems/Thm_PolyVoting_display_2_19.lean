-- Prove2me | Theorems.Thm_PolyVoting_display_2_19
-- name    : PolyVoting.display_2_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:24.000648+00:00
-- url     : https://prove2.me/theorems/5c9d4874-2462-4af8-a121-b8d7a5bad869
-- title:
--   (2.19) — Goldstein–Reinert: $d_W(\pi^\dagger_{k,t},\mathrm{Beta}(n_{k,0},N-n_{k,0}))=O(t^{-1})$
-- statement:
--   Let $(\boldsymbol n^\dagger_t)$ be the Pólya urn with $n^\dagger_{k,0}=n_{k,0}$, with shares $\pi^\dagger_{k,t}$, and let $Z$ have the law $\mathrm{Beta}(n_{k,0},N-n_{k,0})$. For each $k\in[K]$,
--   $$d_W(\pi^\dagger_{k,t},Z)=O(t^{-1})\quad\text{as }t\to\infty.$$
--
--   This is the rate of convergence for the urn. After the random time change it becomes the rate (2.16).
--
--   Differences from the source:
--   - encoding: the Poly(α) rule described by (2.3)–(2.6), K ∈ ℕ₊ bidders, stakes n_{k,t} → `Model μ K α n₀`: the joint conditional one-step law, stakes in Fin K → ℕ, real α ≥ 0 with Real.rpow, and 1 ≤ N; reason: the conditional one-step law and n₀ determine the law of the chain; 1 ≤ N only keeps N_t^{−α} defined
--   - encoding: the Pólya urn with K colours and initial composition n_{k,0} → a `Model` with α = 0 and the same n₀, the Poly(0) instance of the same structure; reason: p.5 identifies α = 0 with the Pólya urn, and at α = 0 the step law is "colour k is drawn with probability n_{k,t}/N_t and one ball of colour k is added"
--   - encoding: d_W(X, ν) real-valued, O(·) as t → ∞ → wassersteinDistance 1 (μ.map X) ν in ℝ≥0∞, and ∃ C, eventually in t, the distance ≤ ENNReal.ofReal (C · rate); reason: the coupling infimum at p = 1 on ℝ is the W1 of Villani; comparing in ℝ≥0∞ keeps an infinite distance from passing the bound
--   - encoding: Beta(n_{k,0}, N − n_{k,0}) for each k → the clause is guarded by 1 ≤ n₀ k and n₀ k < N; reason: the guard only excludes undefined laws: a zero Beta parameter has no density and Mathlib's betaMeasure is then the zero measure
--   - reading: the printed list "(π†k,t, . . . , π†K,t)" → the shares π†_{1,t}, …, π†_{K,t}; reason: the first index is a typo
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, proof of Theorem 6 (i), display (2.19), p.11, citing Goldstein & Reinert (2013)

import Mathlib
import Definitions.Def_PolyVoting_Model
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory ProbabilityTheory Filter
open WassersteinDRO.Duality

namespace PolyVoting

/-- **Display (2.19), Goldstein–Reinert** (Tang & Yao, *Polynomial Voting Rules*,
arXiv:2206.10105v5, p.11): for a Pólya urn `π†`, `d_W(π†_{k,t}, Beta(n_{k,0}, N - n_{k,0})) = O(1 / t)`.

**Formalization Note.** `d_W` is `wassersteinDistance 1` on `ℝ`, valued in `ℝ≥0∞`, of the laws, and
the comparison is made in `ℝ≥0∞`, so an infinite distance would falsify the bound. The guard
`1 ≤ n₀ k`, `n₀ k < N` says that both Beta parameters are positive. It holds for every `k` when
`K ≥ 2` and every `n₀ j ≥ 1`. -/
theorem display_2_19 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℕ} {n₀ : Fin K → ℕ} (U : Model μ K 0 n₀) (k : Fin K)
    (hk : 1 ≤ n₀ k) (hk' : n₀ k < ∑ j, n₀ j) :
    ∃ C : ℝ, ∀ᶠ t : ℕ in atTop,
      wassersteinDistance 1 (μ.map (U.share k t))
          (betaMeasure (n₀ k) (((∑ j, n₀ j : ℕ) : ℝ) - n₀ k)) ≤
        ENNReal.ofReal (C * (t : ℝ) ^ (-1 : ℝ)) := by sorry

end PolyVoting
