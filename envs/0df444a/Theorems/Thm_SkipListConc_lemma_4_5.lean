-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_5
-- name    : SkipListConc.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:53.776784+00:00
-- url     : https://prove2.me/theorems/784f1ef2-4d00-41cf-835f-651a271d258b
-- title:
--   Lemma 4.5 — $D^{\mathrm{Mor}}_x(L)\le 2\sum_{\ell=1}^{L}\min\{f,\sum_{r\le\ell}G_r\}$
-- statement:
--   Fix $0<p<1$, an item $x$ and $f\ge1$. Let $G_r$ be the waiting times of Lemma 2.6, so that the Morris hitting times satisfy $\tau_\ell=1+\sum_{r=1}^{\ell-1}G_r$ for $\ell\ge2$. Then for every $L\ge1$, on every outcome,
--   $$
--   D^{\mathrm{Mor}}_x(L)\ \le\ 2\sum_{\ell=1}^{L}\min\Bigl\{f,\ \sum_{r=1}^{\ell}G_r\Bigr\}.
--   $$
--
--   It reduces the vertical cost of one item to a weighted sum of independent geometric waiting times.
--
--   Differences from the source:
--   - generalization: G_r the independent Geom(p^r) waiting times of Lemma 2.6, under the law of Definition 1.1 → any ℕ∞-valued G_r satisfying the identity τ_ℓ = 1 + ∑_{r<ℓ} G_r, for every realization ξ; reason: the bound is pointwise and uses only the identity; Lemma 2.6 supplies such G_r
--   - generalization: f = f_x → every f ≥ 1; reason: f_x is an arbitrary positive integer, so the source's case is an instance
--   - encoding: integer arithmetic → the inequality in ℕ∞; reason: G_r is ℕ∞-valued (see Lemma 2.6)
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.5, p.24

import Mathlib
import Definitions.Def_SkipListConc_hitTime
import Definitions.Def_SkipListConc_dMor

namespace SkipListConc

/-- Lemma 4.5 (the Morris count as a sum of waiting times) (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), Lemma 4.5, p.24). Let `G_r` be the waiting times of Lemma 2.6, so that
`τ_ℓ = 1 + ∑_{r=1}^{ℓ−1} G_r` for `ℓ ≥ 2`. For every `L ≥ 1`, pointwise,
`D^Mor_x(L) ≤ 2 ∑_{ℓ=1}^{L} min {f, ∑_{r=1}^{ℓ} G_r}`.

**Formalization Note** In `ℕ∞`. The waiting times enter only through the identity of Lemma 2.6,
which is the hypothesis; their law and independence are not needed for this pointwise bound, and
it is stated for every `f ≥ 1` and every noise realization. -/
theorem lemma_4_5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {K : ℕ} {α Ω : Type*}
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (x : α) (G : ℕ → Ω → ℕ∞)
    (hG : ∀ ω : Ω, ∀ ℓ : ℕ, 2 ≤ ℓ →
      hitTime p ξ x ℓ ω = 1 + ∑ r ∈ Finset.Icc 1 (ℓ - 1), G r ω) :
    ∀ f L : ℕ, 1 ≤ f → 1 ≤ L → ∀ ω : Ω,
      ((dMor p ξ x f L ω : ℕ) : ℕ∞) ≤
        2 * ∑ ℓ ∈ Finset.Icc 1 L, min (f : ℕ∞) (∑ r ∈ Finset.Icc 1 ℓ, G r ω) := by sorry

end SkipListConc
