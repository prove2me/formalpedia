-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_5
-- name    : PreservePast.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:33:49.739409+00:00
-- url     : https://prove2.me/theorems/c8dbe0ea-ee07-49c9-a5ec-9708cf06cb74
-- title:
--   Theorem 5 — the bounded-association tolerance window
-- statement:
--   Consider the bounded-association class of §3.2 with $m=2k$ outputs: associations $\|a_i\|\le c<1$, gradient block $\|F\|_F\le\Gamma=3c/2$, all unit queries $p\in\mathbb R^m$, legal updates $\operatorname{rank}[p,W]\le r$, $\|W\|_F\le\sqrt 8$, and regret measured against the best legal update. Fix $0<c<1$ and $0<\delta\le 1/4$. For $d\ge4$, $2\le k\le d$, $2\le r\le\min\{2k,d+1\}$ and $t=\min\{r-1,k,d\}$, uniformly over these parameters,
--   $$B^{\mathrm{after}}_r\Big(\frac{c^2(1-\kappa)}2,\delta\Big)=\Theta_\delta\big(kd\kappa+d\sqrt{kt}\big),\qquad 0\le\kappa\le\tfrac14,$$
--   $$B^{\mathrm{after}}_r\Big(\frac{c^2(1+\Delta)}2,\delta\Big)=\Theta_\delta\big(d\min\{\sqrt{kt},\,t/\Delta\}\big),\qquad 0<\Delta\le\tfrac14,$$
--   and throughout this window
--   $$B^{\mathrm{before}}_r=\Theta_\delta\big(t(k+d)\big).$$
--
--   In balanced dimensions $k\asymp d\asymp N$ at fixed rank, revealing the query after compression costs $\Theta(N^{3/2})$ bits at $\varepsilon=c^2/2$, against $\Theta(N)$ when it is revealed before.
--
--   **Formalization Note** The $m=2k$ outputs are indexed by `Fin k ⊕ Fin k`. The constants are chosen after $\delta$ only, before $c$ and all dimension, rank and tolerance parameters.
--
--   Differences from the source:
--   - encoding: B = Θ_δ(X), uniformly over the parameters → constants lo, hi > 0 chosen after δ only; lo·X ≤ B for every achieving width B and an achieving protocol of width B ≤ hi·X; reason: spells out Θ_δ and avoids the junk value of an infimum over an empty set
--   - encoding: regret at most ε with probability at least 1 − δ for legal updates → the success event is: the block is legal and its regret is at most ε; reason: the decoder can replace an illegal block by 0, so the least width is unchanged
--   - reading: Throughout this window, B_r^before = Θ_δ(t(k + d)) → for every tolerance 3c²/8 ≤ ε ≤ 5c²/8; reason: the window is the set of tolerances c²(1−κ)/2 and c²(1+Δ)/2 of (18), which is this interval (the range of Lemma 9)
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 5, p.8 (PDF p.10), eq. (18); §3.2, p.7 (PDF p.9), eq. (17)

import Mathlib
import Definitions.Def_PreservePast_Supplement_AfterAchieves

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 5 (The bounded-association tolerance window).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 5, p.8 (PDF p.10),
eq. (18); the class is that of §3.2, p.7 (PDF p.9).

For the bounded-association class with `m = 2k` outputs and all unit queries `p ∈ ℝ^m`:
`B_r^after(c²(1−κ)/2, δ) = Θ_δ(kdκ + d√(kt))` for `0 ≤ κ ≤ 1/4`,
`B_r^after(c²(1+Δ)/2, δ) = Θ_δ(d min{√(kt), t/Δ})` for `0 < Δ ≤ 1/4`, and
`B_r^before(ε, δ) = Θ_δ(t(k+d))` for every tolerance `ε` of the window
`3c²/8 ≤ ε ≤ 5c²/8`.

**Formalization Note.** The `m = 2k` outputs are indexed by `Fin k ⊕ Fin k`. `B = Θ_δ(X)` is
stated in the two-part form of the published goal: `lo · X ≤ B` for every achieving width `B`
(arbitrary public coins, coin spaces in `Type`), and an achieving protocol of width `B ≤ hi · X`;
this avoids `sInf ∅`. The constants `lo, hi` are chosen after `δ` only and before `c` and all
dimension, rank and tolerance parameters (`Θ_δ`, "uniformly over these parameters").
`t = tParam r k d = min{r − 1, k, d}`. "Throughout this window" is read as every tolerance
`c²(1−κ)/2`, `0 ≤ κ ≤ 1/4`, and `c²(1+Δ)/2`, `0 < Δ ≤ 1/4`, i.e. `3c²/8 ≤ ε ≤ 5c²/8`. -/
theorem theorem_5 :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ (c : ℝ) (d k r : ℕ), 0 < c → c < 1 → 4 ≤ d → 2 ≤ k → k ≤ d → 2 ≤ r → r ≤ min (2 * k) (d + 1) →
        (∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 / 4 →
          (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (boundedAssocClass (Fin k ⊕ Fin k) d c) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 * (1 - κ) / 2) δ P enc dec →
            lo * (k * d * κ + d * Real.sqrt (k * tParam r k d)) ≤ (B : ℝ)) ∧
          ∃ B : ℕ, (B : ℝ) ≤ hi * (k * d * κ + d * Real.sqrt (k * tParam r k d)) ∧
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (boundedAssocClass (Fin k ⊕ Fin k) d c) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 * (1 - κ) / 2) δ P enc dec) ∧
        (∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
          (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (boundedAssocClass (Fin k ⊕ Fin k) d c) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 * (1 + Δ) / 2) δ P enc dec →
            lo * (d * min (Real.sqrt (k * tParam r k d)) (tParam r k d / Δ)) ≤ (B : ℝ)) ∧
          ∃ B : ℕ, (B : ℝ) ≤ hi * (d * min (Real.sqrt (k * tParam r k d)) (tParam r k d / Δ)) ∧
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (boundedAssocClass (Fin k ⊕ Fin k) d c) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 * (1 + Δ) / 2) δ P enc dec) ∧
        ∀ ε : ℝ, 3 * c ^ 2 / 8 ≤ ε → ε ≤ 5 * c ^ 2 / 8 →
          (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → (Fin k ⊕ Fin k → ℝ) → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            BeforeAchieves (boundedAssocClass (Fin k ⊕ Fin k) d c) (unitQueries (Fin k ⊕ Fin k)) r
              ε δ P enc dec →
            lo * (tParam r k d * (k + d)) ≤ (B : ℝ)) ∧
          ∃ B : ℕ, (B : ℝ) ≤ hi * (tParam r k d * (k + d)) ∧
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → (Fin k ⊕ Fin k → ℝ) → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            BeforeAchieves (boundedAssocClass (Fin k ⊕ Fin k) d c) (unitQueries (Fin k ⊕ Fin k)) r
              ε δ P enc dec := by sorry

end PreservePast.Supplement
