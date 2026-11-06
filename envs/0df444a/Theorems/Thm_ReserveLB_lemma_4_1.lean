-- Prove2me | Theorems.Thm_ReserveLB_lemma_4_1
-- name    : ReserveLB.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:37:13.853001+00:00
-- url     : https://prove2.me/theorems/4a9f7e6a-a2f2-40f5-b64e-5657731ef64a
-- title:
--   Lemma 4.1 — mean-paid original round: column sums at most one and the caps (6), (7)
-- statement:
--   Let virtual classes with speeds $S_h > 0$ satisfy (1), $k \ge 1$, $T > 0$, let the sizes be independent with listed laws, let $\underline v, \underline w$ be lower enclosures of width $\eta = 1/(16(n+1))$ of the risk coefficients, and let $x$ be a fractional point of $\mathcal F_k(T)$ (rows with $\mu$, $\underline v$, $\underline w$, $c$). Then:
--   1. every weighted column (rows divided by $N_h$; means weight $1$, first risks $\min\{N_h, 7\}$ when $N_h \ge 2$, prefix risks $13$ when $\lambda_{rh} \ge 16$, other risk rows $0$) has sum at most one;
--   2. $R_\mu(N) = a_\mu(N) + 2 \le 44/5$ for every $N \ge 1$;
--   3. there is a choice of one pattern $q(j)$ per job with $x_{j q(j)} > 0$ such that, with $R_1 = 33/10$ and $R_p = 152861/26325$,
--   $$
--   \sum_j \mu_{j q(j) h} \le R_\mu(N_h)N_h,\quad \sum_{j:\ f(q(j)) = h}\underline v_{j q(j)} \le R_1 N_h,\quad \sum_j \underline w_{j q(j) r h} \le R_p N_h\ (r < h),\quad \sum_j c_{j q(j)} \le \tfrac{11513}{5000};\tag{6}
--   $$
--   4. for this choice, every first row and every prefix row satisfies
--   $$
--   \text{true total} \le \text{upper total} \le \text{rounded lower-row total} + n\eta, \tag{7}
--   $$
--   where the upper enclosure is $\underline v + \eta$ (resp. $\underline w + \eta$), and the lower enclosure itself in the exact cases.
--
--   The round fixes the comparator-compatible pattern of every original; its row caps are the inputs of the placement and congestion bounds.
--
--   Differences from the source:
--   - generalization: the weighted original columns (of the rounded system, with lower enclosures) have sums at most one → the weighted columns of the true coefficients have sums at most one; reason: lower ≤ true and the weights are nonnegative, so this implies the source's statement
--   - generalization: rational lower enclosures of width η → real lower enclosures with the same width and the same exact cases; reason: the rational enclosures are among them
--   - reading: The supported round selects one complete pattern per original and satisfies the row caps → there exists a selection q(j) with x_{j q(j)} > 0 satisfying the caps (6) and (7); reason: the paper's round is the partition rounding of Section 4.1 applied with the p.7 weights; its output is such a selection
--   - reading: lower enclosures → lower enclosures are nonnegative (part of IsLowerEnclosure); reason: they enclose nonnegative effective sizes from below by positive series (p.13), and the rounding of Section 4.1 is applied to them as nonnegative columns
--   - encoding: upper-enclosure row → the row with v̲ + η (w̲ + η), and with v̲ (w̲) in the exact cases of base one or zero coefficient; reason: p.5: "Base-one and zero cases are exact; elsewhere lower plus η is an upper enclosure"
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 4.1, (6), (7), p.7; rounding weights p.7

import Mathlib
import Definitions.Def_ReserveLB_LawOK
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_ClassStr_Smooth1
import Definitions.Def_ReserveLB_Pattern
import Definitions.Def_ReserveLB_firstActive
import Definitions.Def_ReserveLB_coefMu
import Definitions.Def_ReserveLB_coefV
import Definitions.Def_ReserveLB_coefW
import Definitions.Def_ReserveLB_coefC
import Definitions.Def_ReserveLB_aMu
import Definitions.Def_ReserveLB_eta
import Definitions.Def_ReserveLB_Feasible
import Definitions.Def_ReserveLB_vExact
import Definitions.Def_ReserveLB_wExact
import Definitions.Def_ReserveLB_IsLowerEnclosure
import Definitions.Def_ReserveLB_roundColumn

namespace ReserveLB

open Classical in
/-- **Lemma 4.1 — mean-paid original round.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 4.1, (6), (7), p.7: "The weighted original columns have sums at most one. The
supported round selects one complete pattern per original and satisfies the unweighted rational
lower-enclosure row caps Rµ(N) = aµ(N) + 2 ≤ 44/5, R1 = 33/10, Rp = 152861/26325,
Σ_j cj,q(j) ≤ 11513/5000. (6) The corresponding mean, lower first-risk and lower prefix-risk bounds
are Rµ(Nh)Nh, R1Nh, RpNh. Every first/prefix row of true risks and its upper-enclosure row
therefore satisfy true total ≤ upper total ≤ rounded lower-row total + nη. (7)" Weights: p.7.

With classes satisfying (1), `k ≥ 1`, `T > 0`, jobs with listed laws, lower enclosures `v̲, w̲` of
width `η = 1/(16(n+1))`, and a fractional point `x` of `F_k(T)` (rows with `µ`, `v̲`, `w̲`, `c`):
1. every weighted column (p.7 weights) has sum at most one;
2. `R_µ(N) = a_µ(N) + 2 ≤ 44/5` for every `N ≥ 1`;
3. there is a choice of one pattern `q(j)` per job with `x_(j, q(j)) > 0` such that
   `Σ_j µ_(j,q(j),h) ≤ R_µ(N_h) N_h`, `Σ_(j : f(q(j)) = h) v̲_(j,q(j)) ≤ (33/10) N_h`,
   `Σ_j w̲_(j,q(j),r,h) ≤ (152861/26325) N_h` for `r < h`, and `Σ_j c_(j,q(j)) ≤ 11513/5000`;
4. for that choice, every first row and every prefix row satisfies (7): the true total is at most
   the upper-enclosure total (lower plus `η`, exact in the exact cases), which is at most the
   lower total plus `nη`.

**Formalization Note.** Item 1 is stated with the true coefficients (at least the lower ones).
"The supported round" is read as the existence of the selection. -/
theorem lemma_4_1 (C : ClassStr) (hS : ∀ h, 0 < C.S h) (hC : C.Smooth1) (k : ℕ) (hk : 1 ≤ k)
    (T : ℝ) (hT : 0 < T) {n : ℕ} (law : Fin n → List (ℚ × ℚ)) (hlaw : ∀ j, LawOK (law j))
    (vL : Fin n → Pattern C k → ℝ) (wL : Fin n → Pattern C k → Fin C.L → Fin C.L → ℝ)
    (hL : IsLowerEnclosure C k T (eta n) law vL wL) (x : Fin n → Pattern C k → ℝ)
    (hx : Feasible C k n (fun j q h => coefMu C T (law j) q.1 h) vL wL
      (fun j q => coefC C T (law j) q.1) x) :
    (∀ j (q : Pattern C k), roundColumn C T (law j) q.1 ≤ 1) ∧
    (∀ N : ℕ, 1 ≤ N → aMu N + 2 ≤ 44 / 5) ∧
    ∃ qs : Fin n → Pattern C k, (∀ j, 0 < x j (qs j)) ∧
      (∀ h, ∑ j, coefMu C T (law j) (qs j).1 h ≤ (aMu (C.N h) + 2) * C.N h) ∧
      (∀ h, ∑ j ∈ Finset.univ.filter (fun j => firstActive (qs j).1 = some h), vL j (qs j) ≤
        33 / 10 * C.N h) ∧
      (∀ r h, r < h → ∑ j, wL j (qs j) r h ≤ 152861 / 26325 * C.N h) ∧
      (∑ j, coefC C T (law j) (qs j).1 ≤ 11513 / 5000) ∧
      (∀ h,
        ∑ j ∈ Finset.univ.filter (fun j => firstActive (qs j).1 = some h),
            coefV C T (law j) (qs j).1 ≤
          ∑ j ∈ Finset.univ.filter (fun j => firstActive (qs j).1 = some h),
            (if vExact C T (law j) (qs j).1 then vL j (qs j) else vL j (qs j) + eta n) ∧
        ∑ j ∈ Finset.univ.filter (fun j => firstActive (qs j).1 = some h),
            (if vExact C T (law j) (qs j).1 then vL j (qs j) else vL j (qs j) + eta n) ≤
          ∑ j ∈ Finset.univ.filter (fun j => firstActive (qs j).1 = some h), vL j (qs j) +
            n * eta n) ∧
      (∀ r h, r < h →
        ∑ j, coefW C T (law j) (qs j).1 r h ≤
          ∑ j, (if wExact C T (law j) (qs j).1 r h then wL j (qs j) r h
            else wL j (qs j) r h + eta n) ∧
        ∑ j, (if wExact C T (law j) (qs j).1 r h then wL j (qs j) r h
            else wL j (qs j) r h + eta n) ≤
          ∑ j, wL j (qs j) r h + n * eta n) := by sorry

end ReserveLB
