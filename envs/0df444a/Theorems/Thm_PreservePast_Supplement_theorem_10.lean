-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_10
-- name    : PreservePast.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:36:19.746948+00:00
-- url     : https://prove2.me/theorems/5dc6a36e-d8a0-490b-8db2-4a22318aff67
-- title:
--   Theorem 10 — rank-dependent lower bounds
-- statement:
--   For the paired class (85) (associations $A=c[Z;-Z]$ with unit-row $Z\in\mathbb R^{k\times d}$, $g_0=0$, $\|F\|_F\le\Gamma=3c/2$, $R=3$, queries $p=Sv$ for unit $v\in\mathbb R^k$), $d\ge4$, $k\ge1$, $2\le r\le\min\{2k,d+1\}$, $t=\min\{r-1,k,d\}$, and fixed $0<\delta\le1/4$,
--   $$B^{\mathrm{after}}_r\big(c^2(1-\kappa)/2,\delta\big)\ge c_\delta\{t(k+d)+kd\kappa+d\sqrt{kt}\},\qquad 0\le\kappa\le\tfrac14,$$
--   $$B^{\mathrm{after}}_r\big(c^2(1+\Delta)/2,\delta\big)\ge c_\delta\{t(k+d)+d\min\{\sqrt{kt},t/\Delta\}\},\qquad 0<\Delta\le\tfrac14.$$
--   The constants are independent of rank and aspect ratio. The known-query bound supplies
--   $$B^{\mathrm{after}}_r\ge B^{\mathrm{before}}_r\ge c_\delta\,t(k+d).$$
--
--   These are the converse halves of the tolerance-window law of Theorem 5.
--
--   **Formalization Note** The $2k$ paired outputs are indexed by `Fin k ⊕ Fin k`; $c_\delta$ is chosen after $\delta$ only.
--
--   Differences from the source:
--   - encoding: B ≥ c_δ{…} for the least width → c_δ{…} ≤ B for every achieving width B, with c_δ chosen after δ only; reason: a lower bound on a minimum is a bound on every achieving width
--   - reading: B_r^after ≥ B_r^before ≥ c_δ t(k + d) (89), stated without tolerance → every before-query protocol at a tolerance 3c²/8 ≤ ε ≤ 5c²/8 has width ≥ c_δ t(k+d), and an after-query protocol of width B at any tolerance and failure probability yields a before-query protocol of the same width; reason: the known-query bound is Lemma 9, whose range is this window; the first inequality holds at every tolerance
--   - encoding: regret at most ε with probability at least 1 − δ for legal updates → the success event is: the block is legal and its regret is at most ε; reason: the decoder can replace an illegal block by 0, so the least width is unchanged
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 10, p.29 (PDF p.31), eqs. (87)–(89); class (85) and contract (86), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_PreservePast_Supplement_AfterAchieves

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 10 (Rank-dependent lower bounds).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 10, p.29 (PDF p.31),
eqs. (87)–(89); the class is (85), p.28 (PDF p.30), with the success contract (86).

For the paired class and the paired queries `p = Sv`, `d ≥ 4`, `k ≥ 1`,
`2 ≤ r ≤ min{2k, d+1}`, `t = min{r−1, k, d}` and `0 < δ ≤ 1/4`:
(87) `B_r^after(c²(1−κ)/2, δ) ≥ c_δ{t(k+d) + kdκ + d√(kt)}`, `0 ≤ κ ≤ 1/4`;
(88) `B_r^after(c²(1+Δ)/2, δ) ≥ c_δ{t(k+d) + d min{√(kt), t/Δ}}`, `0 < Δ ≤ 1/4`;
(89) `B_r^after ≥ B_r^before ≥ c_δ t(k+d)`.

**Formalization Note.** The `2k` paired outputs are indexed by `Fin k ⊕ Fin k`. A lower bound on
a minimum width is stated for every achieving width `B` (arbitrary public coins, coin spaces in
`Type`). `c_δ` is chosen after `δ` only, before `c, d, k, r, κ, Δ` ("The constants are
independent of rank and aspect ratio"). (89) is stated in two parts: every before-query protocol
on the window `3c²/8 ≤ ε ≤ 5c²/8` (the range of Lemma 9, the "known-query bound") has width
`≥ c_δ t(k+d)`; and `B_r^after ≥ B_r^before` at every tolerance and failure probability: an
after-query protocol of width `B` yields a before-query protocol of the same width. -/
theorem theorem_10 :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∃ cδ : ℝ, 0 < cδ ∧
      ∀ (c : ℝ) (d k r : ℕ), 0 < c → c < 1 → 4 ≤ d → 1 ≤ k → 2 ≤ r → r ≤ min (2 * k) (d + 1) →
        (∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 / 4 →
          ∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (pairedClass k d c) (pairedQueries k) r (c ^ 2 * (1 - κ) / 2) δ P enc dec →
            cδ * (tParam r k d * (k + d) + k * d * κ + d * Real.sqrt (k * tParam r k d)) ≤
              (B : ℝ)) ∧
        (∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
          ∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (pairedClass k d c) (pairedQueries k) r (c ^ 2 * (1 + Δ) / 2) δ P enc dec →
            cδ * (tParam r k d * (k + d) +
              d * min (Real.sqrt (k * tParam r k d)) (tParam r k d / Δ)) ≤ (B : ℝ)) ∧
        (∀ ε : ℝ, 3 * c ^ 2 / 8 ≤ ε → ε ≤ 5 * c ^ 2 / 8 →
          ∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → (Fin k ⊕ Fin k → ℝ) → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            BeforeAchieves (pairedClass k d c) (pairedQueries k) r ε δ P enc dec →
            cδ * (tParam r k d * (k + d)) ≤ (B : ℝ)) ∧
        ∀ (ε δ' : ℝ) (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (pairedClass k d c) (pairedQueries k) r ε δ' P enc dec →
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → (Fin k ⊕ Fin k → ℝ) → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
              BeforeAchieves (pairedClass k d c) (pairedQueries k) r ε δ' P enc dec := by sorry

end PreservePast.Supplement
