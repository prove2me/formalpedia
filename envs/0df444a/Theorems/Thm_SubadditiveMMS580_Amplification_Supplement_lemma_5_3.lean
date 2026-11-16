-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_5_3
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:59:34.72442+00:00
-- url     : https://prove2.me/theorems/0c97e104-ed01-4a84-9070-44ac8f27c674
-- title:
--   Lemma 5.3 — choices from an additive lower bound: $\tilde v=\lambda z/z(M)$ with threshold $\lambda(\beta-w(H)+\|z\|_\infty)/z(M)$
-- statement:
--   Let $\beta>0$, let $w$ be nonnegative additive coefficients on $M$ with $w(S)\le v(S)$ for every $S\subseteq M$, and let $H\subseteq M$ satisfy $w(H)<\beta$. Let $z$ be nonnegative coefficients with $z(g)\le w(g)$ for every $g$, $z(g)=0$ on $H$, and $z(M)>0$. For every $\lambda>0$ let
--   $$\tilde v=\frac{\lambda z}{z(M)},\qquad \tau=\lambda\,\frac{\beta-w(H)+\|z\|_\infty}{z(M)}.$$
--   Then $\tilde v(M)=\lambda$ and $(H,\tilde v,\tau)$ satisfies condition (16) for $v$ and $\beta$: for every $B\subseteq M\setminus H$, $\tilde v(B)>\tau-\|\tilde v\|_\infty$ implies $v(H\cup B)\ge\beta$.
--
--   It produces the reserving choices used in §5.4 for the proof of Theorem 1.3.
--
--   Differences from the source:
--   - generalization: v a valuation (normalized, monotone, ℝ≥0-valued) → v an arbitrary real set function; reason: Lemma 5.3 uses only w ≤ v and additivity of w; every source valuation is such a set function
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma 5.3, p. 33 (PDF p. 33)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Reservation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation

open MultiAllocToAlloc.Subadditive MeasureTheory

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma 5.3 (Li–Sun, STOC 2027 submission #580, p. 33): let `β > 0`, let `w ≤ v` be a
nonnegative additive lower bound on `M`, and let `H ⊆ M` satisfy `w(H) < β`. Let `z ≤ w` be
nonnegative additive coefficients supported outside `H` with `z(M) > 0`. For every `λ > 0`, with
`ṽ = λ z / z(M)` and `τ = λ (β − w(H) + ‖z‖∞) / z(M)`, we have `ṽ(M) = λ` and `(H, ṽ, τ)`
satisfies (16). -/
theorem lemma_5_3 {m : ℕ} (β : ℝ) (hβ : 0 < β) (v : Finset (Fin m) → ℝ) (w : Fin m → ℝ)
    (hw : ∀ g, 0 ≤ w g) (hwv : ∀ S : Finset (Fin m), ∑ g ∈ S, w g ≤ v S)
    (H : Finset (Fin m)) (hH : ∑ g ∈ H, w g < β)
    (z : Fin m → ℝ) (hz : ∀ g, 0 ≤ z g) (hzw : ∀ g, z g ≤ w g) (hzH : ∀ g ∈ H, z g = 0)
    (hzpos : 0 < ∑ g, z g) (lam : ℝ) (hlam : 0 < lam) :
    (∑ g, lam * z g / ∑ g', z g') = lam ∧
    SatisfiesReservation v β
      ⟨H, fun g => lam * z g / ∑ g', z g',
        lam * (β - ∑ g ∈ H, w g + supNorm z) / ∑ g', z g'⟩ := by sorry

end SubadditiveMMS580.Amplification.Supplement
