-- Prove2me | Theorems.Thm_ReserveLB_lemma_3_1
-- name    : ReserveLB.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:34:11.658472+00:00
-- url     : https://prove2.me/theorems/5305be12-c385-4ae0-9c09-d96034d369ae
-- title:
--   Lemma 3.1 — strict-target necessity: a cheap smoothed graph gives an integral point of $\mathcal F_k(T)$
-- statement:
--   Let virtual classes with speeds $S_h > 0$ and counts $N_h$ satisfy (1), let $k \ge 1$ and $T > 0$, and let the sizes $X_1, \dots, X_n$ be independent with listed laws. Let $\tau$ give every job a nonempty set $\tau(j)$ of at most $k$ virtual machines, with expected optimal integral cost
--   $$
--   B = \mathbb E\,T_\tau(X) \le \tfrac{9}{10}\,T .
--   $$
--   Then the capped patterns $q_j(h) = \min\{2, |\tau(j) \cap C_h|\}$ are patterns, and the integral point that chooses $q_j$ for job $j$ satisfies every row of (4) with the true coefficients $\mu, v, w, c$:
--   $$
--   \sum_j \mu_{j q_j h} \le a_\mu(N_h)N_h,\quad \sum_{j:\ f(q_j) = h} v_{j q_j} \le a_1(N_h)N_h,\quad \sum_j w_{j q_j r h} \le a_p N_h\ (r<h),\quad \sum_j c_{j q_j} \le a_e .
--   $$
--
--   Since the lower enclosures are at most the true coefficients, the same point is feasible for the paper's $\mathcal F_k(T)$ with any lower enclosures. This is the necessity half of the target search.
--
--   Differences from the source:
--   - generalization: an integral feasible point of F_k(T), whose first and prefix rows use lower enclosures v̲, w̲ → the point satisfies the rows with the true coefficients v, w; reason: v̲ ≤ v and w̲ ≤ w and x ≥ 0, so it is feasible for every lower enclosure (p.6: "Lower enclosures preserve every row")
--   - reading: a smoothed same-budget graph … induces an integral point → virtual classes with positive speeds satisfying (1); a reservation of nonempty sets of at most k virtual machines per job; the induced point is the capped pattern q_j(h) = min{2, |τ(j) ∩ C_h|}; reason: proof, p.5: "Keep its capped patterns"; p.5: "Capping the multiplicity records a comparator's pattern"
--   - encoding: expected optimal integral cost B, original sizes with listed laws → prodExpect law (Tsig vspeed τ), laws as lists of rational atoms; reason: exact product-law expectation; same instances
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 3.1, p.5; setting and system (4), p.5

import Mathlib
import Definitions.Def_ReserveLB_LawOK
import Definitions.Def_ReserveLB_prodExpect
import Definitions.Def_ReserveLB_Tsig
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_ClassStr_VM
import Definitions.Def_ReserveLB_ClassStr_vspeed
import Definitions.Def_ReserveLB_ClassStr_Smooth1
import Definitions.Def_ReserveLB_Pattern
import Definitions.Def_ReserveLB_coefMu
import Definitions.Def_ReserveLB_coefV
import Definitions.Def_ReserveLB_coefW
import Definitions.Def_ReserveLB_coefC
import Definitions.Def_ReserveLB_Feasible

namespace ReserveLB

/-- **Lemma 3.1 — strict-target necessity.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 3.1, p.5: "A smoothed same-budget graph of expected optimal integral cost
B ≤ 9T/10 induces an integral feasible point of Fk(T)." Setting: Section 3, p.5 ("Fix T > 0",
patterns, portions, coefficients, system (4)); proof, p.5: "Keep its capped patterns".

Let the virtual classes satisfy (1) with positive speeds, `k ≥ 1`, `T > 0`, and let the jobs be
independent with listed laws. Let `τ` give every job a nonempty set of at most `k` virtual machines
with `E T_τ(X) ≤ 9T/10`. Then the capped patterns `q_j(h) = min{2, |τ(j) ∩ C_h|}` are patterns,
and their indicator point satisfies every row of (4) with the true coefficients `µ, v, w, c`.

**Formalization Note.** True coefficients are at least their lower enclosures (and nonnegative
weights), so this gives the integral feasible point of `F_k(T)` with every lower enclosure. -/
theorem lemma_3_1 (C : ClassStr) (hS : ∀ h, 0 < C.S h) (hC : C.Smooth1) (k : ℕ) (hk : 1 ≤ k)
    (T : ℝ) (hT : 0 < T) {n : ℕ} (law : Fin n → List (ℚ × ℚ)) (hlaw : ∀ j, LawOK (law j))
    (τ : Fin n → Finset C.VM) (hτ : ∀ j, (τ j).Nonempty ∧ (τ j).card ≤ k)
    (hB : prodExpect law (Tsig C.vspeed τ) ≤ 9 * T / 10) :
    ∃ qs : Fin n → Pattern C k,
      (∀ j h, ((qs j).1 h : ℕ) = min 2 ((τ j).filter fun v => v.1 = h).card) ∧
      Feasible C k n (fun j q h => coefMu C T (law j) q.1 h) (fun j q => coefV C T (law j) q.1)
        (fun j q r h => coefW C T (law j) q.1 r h) (fun j q => coefC C T (law j) q.1)
        (fun j q => if q = qs j then 1 else 0) := by sorry

end ReserveLB
