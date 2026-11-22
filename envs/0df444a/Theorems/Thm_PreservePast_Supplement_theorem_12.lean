-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_12
-- name    : PreservePast.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:37:27.719789+00:00
-- url     : https://prove2.me/theorems/cafbdd98-8d3f-4b27-aaf8-70673c3e9d3b
-- title:
--   Theorem 12 — unknown shared covariance
-- statement:
--   In the parameter range of Theorem 5 ($m=2k$, $d\ge4$, $2\le k\le d$, $2\le r\le\min\{2k,d+1\}$, $t=\min\{r-1,k,d\}$, $0<c<1$, $0<\delta\le1/4$, $\Gamma=3c/2$, $\beta=5c/2$), let all outputs share one covariance, so that the loss is $f_p(W)=\tfrac12\operatorname{tr}(WQW^\top)-\langle F+pa^\top,W\rangle$. Fix public constants $0<q_-\le1\le q_+<\infty$ and suppose
--   $$q_-I\preceq Q\preceq q_+I,\qquad \|Q^{-1/2}a\|\le c,\qquad \|FQ^{-1/2}\|_F\le\Gamma,\qquad q_-\ge\beta^2/8 .$$
--   Both $Q$ and $a$ may be private. For $3c^2/8\le\varepsilon\le5c^2/8$,
--   $$B^{\mathrm{after}}_r(\varepsilon,\delta)=\Theta_{\delta,q_-,q_+}\big(t(k+d)\big),\qquad B^{\mathrm{before}}_r(\varepsilon,\delta)=\Theta_{\delta,q_-,q_+}\big(t(k+d)\big).$$
--   The upper code is deterministic and succeeds for every query with the same finite message.
--
--   With a shared covariance, a single low-dimensional subspace of the input space serves every query, so an unknown query costs no more than a known one.
--
--   **Formalization Note** The outputs are indexed by `Fin k ⊕ Fin k`. The constants are chosen after $\delta,q_-,q_+$ and before $c$ and the other parameters.
--
--   Differences from the source:
--   - encoding: B^after = Θ(t(k+d)), B^before = Θ(t(k+d)), with a deterministic upper code succeeding for every query with the same message → lo·t(k+d) ≤ B for every after-query and every before-query achieving width, and one deterministic query-blind code of width ≤ hi·t(k+d); reason: the deterministic query-blind code is both an after-query and a before-query protocol
--   - encoding: ‖Q^{-1/2}a‖ ≤ c and ‖FQ^{-1/2}‖_F ≤ Γ → aᵀQ⁻¹a ≤ c² and tr(FQ⁻¹Fᵀ) ≤ Γ²; reason: the same conditions, squared, without a matrix square root
--   - encoding: regret at most ε with probability at least 1 − δ for legal updates → the success event is: the block is legal and its regret is at most ε; reason: the decoder can replace an illegal block by 0, so the least width is unchanged
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 12, p.41 (PDF p.43), eq. (125); Appendix F, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_PreservePast_Supplement_AfterAchieves

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 12 (Unknown shared covariance).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 12, p.41 (PDF p.43), eq. (125);
parameter range of Appendix F, p.39 (PDF p.41).

Fix public `0 < q₋ ≤ 1 ≤ q₊`. For the class of histories with one private covariance shared by
all `m = 2k` outputs, `q₋ I ⪯ Q ⪯ q₊ I`, `‖Q^{-1/2}a‖ ≤ c`, `‖F Q^{-1/2}‖_F ≤ Γ = 3c/2`,
`q₋ ≥ β²/8` with `β = 5c/2`, and `3c²/8 ≤ ε ≤ 5c²/8`:
`B_r^after(ε, δ) = Θ_{δ,q₋,q₊}(t(k+d))` and `B_r^before(ε, δ) = Θ_{δ,q₋,q₊}(t(k+d))`, and the upper
code is deterministic and succeeds for every query with the same message.

**Formalization Note.** The `m = 2k` outputs are indexed by `Fin k ⊕ Fin k`; `β = 5c/2` and
`Γ = 3c/2` are the values fixed in Appendix F, p.39. The constants `lo, hi` are chosen after
`δ, q₋, q₊` and before `c, d, k, r, ε`. The two lower bounds hold for every achieving width
(arbitrary public coins, coin spaces in `Type`); the single upper bound is a deterministic
query-blind code (`DetAfterAchieves`), which is in particular an after-query and a before-query
protocol. `t = tParam r k d`. -/
theorem theorem_12 :
    ∀ δ qlo qhi : ℝ, 0 < δ → δ ≤ 1 / 4 → 0 < qlo → qlo ≤ 1 → 1 ≤ qhi →
      ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ (c : ℝ) (d k r : ℕ) (ε : ℝ), 0 < c → c < 1 → 4 ≤ d → 2 ≤ k → k ≤ d → 2 ≤ r → r ≤ min (2 * k) (d + 1) →
        (5 * c / 2) ^ 2 / 8 ≤ qlo → 3 * c ^ 2 / 8 ≤ ε → ε ≤ 5 * c ^ 2 / 8 →
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            AfterAchieves (sharedCovClass (Fin k ⊕ Fin k) d c qlo qhi)
              (unitQueries (Fin k ⊕ Fin k)) r ε δ P enc dec →
            lo * (tParam r k d * (k + d)) ≤ (B : ℝ)) ∧
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : AssocHistory (Fin k ⊕ Fin k) d → (Fin k ⊕ Fin k → ℝ) → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            BeforeAchieves (sharedCovClass (Fin k ⊕ Fin k) d c qlo qhi)
              (unitQueries (Fin k ⊕ Fin k)) r ε δ P enc dec →
            lo * (tParam r k d * (k + d)) ≤ (B : ℝ)) ∧
        ∃ B : ℕ, (B : ℝ) ≤ hi * (tParam r k d * (k + d)) ∧
          ∃ (enc : AssocHistory (Fin k ⊕ Fin k) d → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → (Fin k ⊕ Fin k → ℝ) → Matrix (Fin k ⊕ Fin k) (Fin d) ℝ),
            DetAfterAchieves (sharedCovClass (Fin k ⊕ Fin k) d c qlo qhi)
              (unitQueries (Fin k ⊕ Fin k)) r ε enc dec := by sorry

end PreservePast.Supplement
