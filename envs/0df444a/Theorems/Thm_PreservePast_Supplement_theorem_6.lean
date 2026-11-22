-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_6
-- name    : PreservePast.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:34:19.66429+00:00
-- url     : https://prove2.me/theorems/ed22bf58-15d1-4457-b653-6550098f1b18
-- title:
--   Theorem 6 — memory with shared association rows
-- statement:
--   Under the assumptions of Theorem 5 ($0<c<1$, $0<\delta\le1/4$, $d\ge4$, $2\le k\le d$, $2\le r\le\min\{2k,d+1\}$, $t=\min\{r-1,k,d\}$), restrict the bounded-association class to histories whose association matrix has at most $g$ distinct rows, $1\le g\le 2k$, keeping $F$ arbitrary within $\|F\|_F\le 3c/2$. At $\varepsilon=c^2/2$,
--   $$B^{\mathrm{after}}_{\le g}=\Theta_\delta\Big(t(k+d)+d\sqrt{g\min\{t,g\}}\Big),\qquad B^{\mathrm{before}}_{\le g}=\Theta_\delta\big(t(k+d)\big).$$
--
--   At fixed rank in balanced dimensions the cost is $\Theta(N\sqrt g)$, interpolating between linear and $N^{3/2}$ memory.
--
--   **Formalization Note** The $m=2k$ outputs are indexed by `Fin k ⊕ Fin k`. The constants are chosen after $\delta$ only, before $c$ and all dimension, rank and tolerance parameters. Which outputs share a row is private.
--
--   Differences from the source:
--   - encoding: B = Θ_δ(X), uniformly over the parameters → constants lo, hi > 0 chosen after δ only; lo·X ≤ B for every achieving width B and an achieving protocol of width B ≤ hi·X; reason: spells out Θ_δ and avoids the junk value of an infimum over an empty set
--   - encoding: regret at most ε with probability at least 1 − δ for legal updates → the success event is: the block is legal and its regret is at most ε; reason: the decoder can replace an illegal block by 0, so the least width is unchanged
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 6, p.9 (PDF p.11), eq. (19)

import Mathlib
import Definitions.Def_PreservePast_Supplement_AfterAchieves

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 6 (Memory with shared association rows).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 6, p.9 (PDF p.11), eq. (19).

Under Theorem 5's assumptions, for the bounded-association class restricted to at most `g`
distinct association rows, `1 ≤ g ≤ 2k`, at `ε = c²/2`:
`B_{≤g}^after = Θ_δ(t(k+d) + d√(g min{t, g}))` and `B_{≤g}^before = Θ_δ(t(k+d))`.

**Formalization Note.** The `m = 2k` outputs are indexed by `Fin k ⊕ Fin k`. `B = Θ_δ(X)` is
stated in the two-part form of the published goal: `lo · X ≤ B` for every achieving width `B`
(arbitrary public coins, coin spaces in `Type`), and an achieving protocol of width `B ≤ hi · X`;
this avoids `sInf ∅`. The constants `lo, hi` are chosen after `δ` only and before `c` and all
dimension, rank and tolerance parameters (`Θ_δ`, "uniformly over these parameters").
`t = tParam r k d = min{r − 1, k, d}`. The constants are also chosen before `g`. -/
theorem theorem_6 :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ (c : ℝ) (d k r g : ℕ), 0 < c → c < 1 → 4 ≤ d → 2 ≤ k → k ≤ d → 2 ≤ r → r ≤ min (2 * k) (d + 1) →
        1 ≤ g → g ≤ 2 * k →
        ((∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (sharedRowClass (Fin k ⊕ Fin k) d c g) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 / 2) δ P enc dec →
            lo * (tParam r k d * (k + d) + d * Real.sqrt (g * min (tParam r k d) g)) ≤ (B : ℝ)) ∧
          ∃ B : ℕ, (B : ℝ) ≤
              hi * (tParam r k d * (k + d) + d * Real.sqrt (g * min (tParam r k d) g)) ∧
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (sharedRowClass (Fin k ⊕ Fin k) d c g) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 / 2) δ P enc dec) ∧
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → (Fin k ⊕ Fin k → ℝ) → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            BeforeAchieves (sharedRowClass (Fin k ⊕ Fin k) d c g) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 / 2) δ P enc dec →
            lo * (tParam r k d * (k + d)) ≤ (B : ℝ)) ∧
          ∃ B : ℕ, (B : ℝ) ≤ hi * (tParam r k d * (k + d)) ∧
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → (Fin k ⊕ Fin k → ℝ) → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            BeforeAchieves (sharedRowClass (Fin k ⊕ Fin k) d c g) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 / 2) δ P enc dec := by sorry

end PreservePast.Supplement
