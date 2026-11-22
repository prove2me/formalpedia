-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_11
-- name    : PreservePast.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:37:02.685564+00:00
-- url     : https://prove2.me/theorems/23617e68-586d-4f0b-aed8-8f30d393d59a
-- title:
--   Theorem 11 — stability at the original center
-- statement:
--   Under the coefficient bounds and parameter assumptions of Theorem 5 ($\|a_i\|\le c<1$, $\|F\|_F\le 3c/2$, $0<\delta\le1/4$, $d\ge4$, $2\le k\le d$, $2\le r\le\min\{2k,d+1\}$, $t=\min\{r-1,k,d\}$), allow arbitrary private row metrics $Q_i$ in the loss
--   $$f_p(W)=\frac12\sum_i w_i^\top Q_iw_i-\langle F+\operatorname{diag}(p)A,W\rangle$$
--   with $\|Q_i-I\|_{\mathrm{op}}\le\eta\le1/64$. At the unchanged tolerance,
--   $$B^{\mathrm{after}}_\eta(c^2/2,\delta)=\Theta_\delta\big(kd\eta+d\sqrt{kt}\big).$$
--
--   Even a scalar shift of the metric lowers the equivalent isotropic tolerance, which is what forces the $kd\eta$ term.
--
--   **Formalization Note** The $m=2k$ outputs are indexed by `Fin k ⊕ Fin k`. The constants are chosen after $\delta$ only, before $c$ and all dimension, rank and tolerance parameters. The constants are also chosen before $\eta$.
--
--   Differences from the source:
--   - encoding: B = Θ_δ(X), uniformly over the parameters → constants lo, hi > 0 chosen after δ only; lo·X ≤ B for every achieving width B and an achieving protocol of width B ≤ hi·X; reason: spells out Θ_δ and avoids the junk value of an infimum over an empty set
--   - encoding: regret at most ε with probability at least 1 − δ for legal updates → the success event is: the block is legal and its regret is at most ε; reason: the decoder can replace an illegal block by 0, so the least width is unchanged
--   - encoding: arbitrary private Q_i with ‖Q_i − I‖_op ≤ η → symmetric Q_i with ‖Q_i − I‖_op ≤ η; reason: Q_i is a diagonal block of the row covariance Σ_i, hence symmetric
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 11, p.39 (PDF p.41); loss (120)

import Mathlib
import Definitions.Def_PreservePast_Supplement_AfterAchieves

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 11 (Stability at the original center).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 11, p.39 (PDF p.41); the loss
is (120).

Under Theorem 5's coefficient bounds and parameter assumptions, with arbitrary private symmetric
row metrics `‖Q_i − I‖_op ≤ η ≤ 1/64`, at the unchanged tolerance `c²/2`:
`B_η^after(c²/2, δ) = Θ_δ(kdη + d√(kt))`.

**Formalization Note.** The `m = 2k` outputs are indexed by `Fin k ⊕ Fin k`. `B = Θ_δ(X)` is
stated in the two-part form of the published goal: `lo · X ≤ B` for every achieving width `B`
(arbitrary public coins, coin spaces in `Type`), and an achieving protocol of width `B ≤ hi · X`;
this avoids `sInf ∅`. The constants `lo, hi` are chosen after `δ` only and before `c` and all
dimension, rank and tolerance parameters (`Θ_δ`, "uniformly over these parameters").
`t = tParam r k d = min{r − 1, k, d}`. The constants are also chosen before `η`. The row metrics `Q_i` are
symmetric (they are blocks of the covariances `Σ_i`). -/
theorem theorem_11 :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ (c : ℝ) (d k r : ℕ) (η : ℝ), 0 < c → c < 1 → 4 ≤ d → 2 ≤ k → k ≤ d → 2 ≤ r → r ≤ min (2 * k) (d + 1) →
        0 ≤ η → η ≤ 1 / 64 →
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (metricAssocClass (Fin k ⊕ Fin k) d c η) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 / 2) δ P enc dec →
            lo * (k * d * η + d * Real.sqrt (k * tParam r k d)) ≤ (B : ℝ)) ∧
        ∃ B : ℕ, (B : ℝ) ≤ hi * (k * d * η + d * Real.sqrt (k * tParam r k d)) ∧
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (metricAssocClass (Fin k ⊕ Fin k) d c η) (unitQueries (Fin k ⊕ Fin k)) r
              (c ^ 2 / 2) δ P enc dec := by sorry

end PreservePast.Supplement
