-- Prove2me | Theorems.Thm_PointRedemption_eq_22
-- name    : PointRedemption.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:27.044989+00:00
-- url     : https://prove2.me/theorems/03f59dd8-26e0-4ddf-b0d2-0a4ae517ba52
-- title:
--   Eq. (22), App. p. 5 — the blackout price is the unique solution of (3) and satisfies its first-order condition (corrected: $\bar F(\Delta_{t-1}(y))>0$)
-- statement:
--   Consider the point-redemption pricing model in which $F$ has an increasing failure rate and the density $f$ is differentiable at every $p>0$ with $\bar F(p)>0$. Let $t\ge1$, $y\ge1$ and $\Delta=\Delta_{t-1}(y)$ with $\bar F(\Delta)>0$. Then the blackout problem (3),
--
--   $$\max_{p\in\mathbb R}\ \lambda\bar F(p)\big(p+V_{t-1}(y-1)\big)+\big(1-\lambda\bar F(p)\big)V_{t-1}(y),$$
--
--   has a unique maximizer $p^c=p^c_t(y)$, and every maximizer satisfies $\Delta<p^c$, $\bar F(p^c)>0$ and the first-order condition
--
--   $$1-\frac{f(p^c)}{\bar F(p^c)}\,(p^c-\Delta)=0.$$
--
--   The one-period blackout price is the price the seller would charge in period $t$ if points were not accepted in that period only, keeping the continuation values $V_{t-1}$ of the model with point redemption. Proposition 1 compares the optimal price with it.
--
--   **Formalization Note** $\Delta$ is the dynamic program's marginal value $V_{t-1}(y)-V_{t-1}(y-1)$, not an arbitrary real. Uniqueness is the paper's "Let $p^c_t(y)$ be the solution to (3)" (p. 14).
--
--   Differences from the source:
--   - correction: no condition on the marginal value Δ_{t−1}(y) → 0 < F̄(Δ_{t−1}(y)); reason: false as printed: F = U[0,1], G = U[0,2], q = 1, β̄ = 1, λ = 1/2, R = 10, (t, y) = (2, 1) satisfy A1–A3, Δ_1(1) = V_1(1) ≈ 1.262 ≥ 1, and every p ≥ 1 maximizes both J_2(·,1) on [0, ∞) and (3), so uniqueness, (22) and Proposition 1 fail
--   - reading: "Let p^c_t(y) be the solution to (3)" → the unique existence of a maximizer of (3) is part of the conclusion; reason: the definite article presupposes a unique solution; the item states it
--   - generalization: the standing assumptions A1–A3 of Theorem 1 (p. 14: "Based on Theorem 1") → only A1 for F and the regularity of f; reason: the blackout problem involves only F; every instance with A1–A3 satisfies the weaker hypotheses
--   - generalization: (22) for the blackout price → also Δ < p^c and F̄(p^c) > 0 for every maximizer; reason: these make the quotient in (22) well defined; the specialization to the paper's claim is the last conjunct
--   - reading: densities with no regularity stated → f differentiable at every p > 0 with F̄(p) > 0; reason: as for Theorem 1: the first-order condition needs a derivative at p^c
--   - encoding: (3): max_p over p as printed → IsMaxOn over Set.univ (all real p); reason: as printed; (1) itself restricts to p ≥ 0 (Set.Ici 0)
--   - encoding: β̄(q) at the fixed q; t = 1, …, T periods with horizon T → βbar a number in [0,1] with β = 1 − βbar; t ≥ 1 counts periods to go, no horizon T; reason: the paper fixes q and writes β̄ for β̄(q) (p. 11); T only bounds t, so every t ≥ 1 is an instance of some horizon
--   - reading: R, the reimbursement, with no sign stated → R ≥ 0 (a field of the model); reason: R is revenue from the point issuer; Prop. 5(b) writes "any reimbursement rate R > 0"
-- source:
--   Chung–Ahn–Chun, Dynamic Pricing with Point Redemption, SSRN 3426903 (KAIST WP KCB-WP-2019-013); MSOM (2022), doi:10.1287/msom.2021.1067, Appendix A, proof of Proposition 1, eq. (22), App. p. 5 (PDF 40); blackout problem (3) and the definition of p^c_t(y), p. 14 (PDF 15)

import Mathlib
import Definitions.Def_PointRedemption_Model

namespace PointRedemption

open MeasureTheory ProbabilityTheory LariviereIGFR.Char

/-- **Eq. (22)** (proof of Proposition 1, corrected), Chung–Ahn–Chun, *Dynamic Pricing with
Point Redemption*, SSRN 3426903; MSOM (2022), doi:10.1287/msom.2021.1067, Appendix A, App. p. 5
(PDF 40), with the definition of the blackout price on p. 14 (PDF 15). If `F` is IFR and `f` is
regular, then for `t ≥ 1`, `y ≥ 1` with `Δ = Δ_{t−1}(y)` and `F̄(Δ) > 0`, the blackout problem (3)
has a unique maximizer `p^c` over all real `p`, and it satisfies `Δ < p^c`, `F̄(p^c) > 0` and the
first-order condition `1 − (f(p^c)/F̄(p^c))(p^c − Δ) = 0`.

**Formalization Note.** Correction: `F̄(Δ_{t−1}(y)) > 0` is added (with `F = U[0,1]` and
`Δ ≥ 1` every `p ≥ 1` maximizes (3) and (22) fails). Uniqueness is the paper's "Let `p^c_t(y)` be
the solution to (3)". `Δ` is the dynamic program's marginal value, not an arbitrary real. -/
theorem eq_22 (P : Params) (hF : IsIFR P.μV P.f) (hreg : P.RegF)
    (t y : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y) (hΔ : 0 < P.Fbar (P.Δ (t - 1) y)) :
    (∃! pc : ℝ, IsMaxOn (fun x => P.Jc t x y) Set.univ pc) ∧
      ∀ pc : ℝ, IsMaxOn (fun x => P.Jc t x y) Set.univ pc →
        P.Δ (t - 1) y < pc ∧ 0 < P.Fbar pc ∧
          1 - P.f pc / P.Fbar pc * (pc - P.Δ (t - 1) y) = 0 := by sorry

end PointRedemption
