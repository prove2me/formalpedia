-- Prove2me | Theorems.Thm_ReserveLB_lemma_2_1_polytime
-- name    : ReserveLB.lemma_2_1_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:32:04.743489+00:00
-- url     : https://prove2.me/theorems/3e53cc04-fb86-4480-b87e-bffeac58b440
-- title:
--   Lemma 2.1 — polynomial whole-job recourse within $D_\sigma(x) + q$
-- statement:
--   There is a deterministic algorithm, running in time polynomial in the binary input, that reads positive rational speeds $s_1, \dots, s_m$ ($m \ge 1$), nonnegative rational sizes $x_1, \dots, x_n$ and a reservation $\sigma$ (every $\sigma(j)$ a nonempty set of machines) and outputs a whole-job assignment $\pi$ with $\pi(j) \in \sigma(j)$ for every job, such that for every $q \ge 0$ with $x_j / s_i \le q$ for all $j$ and all $i \in \sigma(j)$,
--   $$
--   \max_i \sum_{j:\ \pi(j) = i}\frac{x_j}{s_i} \le D_\sigma(x) + q,
--   $$
--   where $D_\sigma(x)$ is the fractional volume threshold.
--
--   This is the polynomial recourse used by the decoder of Theorem 1.1. The companion item `ReserveLB.lemma_2_1` is the rounding statement of the first sentence of Lemma 2.1.
--
--   Differences from the source:
--   - encoding: polynomial recourse → ∃ dec with Turing.TM2ComputableInPolyTime encRecIn encListNat dec (rational speeds, sizes and reservation lists in binary); reason: Mathlib's Turing-machine model; binary numbers make the input length the bit size
--   - encoding: written arcs σ(j) ⊆ [m], nonempty; every written arc has time at most q → reservation lists of indices < m, nonempty, read as sets; the bound holds for every real q ≥ every x_j/s_i with i ∈ σ(j); reason: Lean convention; same instances
--   - reading: q, an upper bound on the written arc times → a real q with 0 ≤ q; reason: q is a processing time and so nonnegative; with n = 0 the arc condition is vacuous and a negative q would make the bound read 0 ≤ q, which is false
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.1, second sentence, p.3; Section 6.2, p.13

import Mathlib
import Definitions.Def_ReserveLB_Dsig
import Definitions.Def_ReserveLB_resOf
import Definitions.Def_ReserveLB_admissibleRes
import Definitions.Def_ReserveLB_validAssign
import Definitions.Def_ReserveLB_listMakespan
import Definitions.Def_ReserveLB_encRecIn
import Definitions.Def_ReserveLB_encListNat
import Definitions.Def_OnlineCRS_Combine_Sym

namespace ReserveLB

/-- **Lemma 2.1, second sentence — polynomial whole-job recourse within `D_σ(x) + q`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.1, p.3: "Consequently, if every written arc has time at most q, polynomial recourse
costs at most Dσ(x) + q."; Section 6.2, p.13 (exact max flow and slot matching).

Some map `dec`, computable by a Turing machine in time polynomial in the binary input, reads speeds
`s_1, …, s_m > 0`, sizes `x_1, …, x_n ≥ 0` and reservations `σ(j)` (nonempty lists of machine
indices), and returns a whole-job assignment inside the reservations whose makespan is at most
`D_σ(x) + q` for every time bound `q ≥ 0` that bounds every written arc time `x_j / s_i`, `i ∈ σ(j)`.
(`q` is a time, so `q ≥ 0`; with no jobs the arc condition is vacuous and a negative `q` would
make the bound `0 ≤ q` false.)

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with the binary
encodings `encRecIn`, `encListNat`. Inputs are rational; the reservation of job `j` is entry `j`. -/
theorem lemma_2_1_polytime :
    ∃ dec : List ℚ × List ℚ × List (List ℕ) → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encRecIn encListNat dec) ∧
      ∀ (s x : List ℚ) (res : List (List ℕ)), s ≠ [] → (∀ a ∈ s, 0 < a) → (∀ a ∈ x, 0 ≤ a) →
        admissibleRes s.length x.length s.length res →
        validAssign x.length res (dec (s, x, res)) ∧
        ∀ q : ℝ, 0 ≤ q → (∀ (j : Fin x.length) (i : Fin s.length), i ∈ resOf s.length x.length res j →
            ((x.get j : ℚ) : ℝ) / ((s.get i : ℚ) : ℝ) ≤ q) →
          listMakespan (fun i : Fin s.length => ((s.get i : ℚ) : ℝ)) (dec (s, x, res))
              (fun j : Fin x.length => ((x.get j : ℚ) : ℝ)) ≤
            Dsig (fun i : Fin s.length => ((s.get i : ℚ) : ℝ)) (resOf s.length x.length res)
              (fun j : Fin x.length => ((x.get j : ℚ) : ℝ)) + q := by sorry

end ReserveLB
