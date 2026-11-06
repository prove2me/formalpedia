-- Prove2me | Theorems.Thm_ReserveLB_lemma_2_1
-- name    : ReserveLB.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:27.983954+00:00
-- url     : https://prove2.me/theorems/058ed22a-081c-4f1c-9afb-e15a539a6dc7
-- title:
--   Lemma 2.1 — whole-job rounding to loads $L_i + q_i$
-- statement:
--   Let $p_{ij} \ge 0$ be the time of job $j$ on machine $i$, and let $y_{ij} \ge 0$ be a fractional assignment with $\sum_i y_{ij} = 1$ for every job $j$. Put
--   $$
--   L_i = \sum_j p_{ij}\, y_{ij},\qquad q_i = \max\{p_{ij} : y_{ij} > 0\}
--   $$
--   (the load of machine $i$ and its largest supported job time; $q_i = 0$ if no job is supported at $i$). Then there is a whole-job assignment $\pi$, using only supported arcs ($y_{\pi(j) j} > 0$ for every $j$), with
--   $$
--   \sum_{j:\ \pi(j) = i} p_{ij} \le L_i + q_i \qquad\text{for every machine } i .
--   $$
--
--   This is the rounding behind whole-job recourse: a fractional routing of the sizes is turned into an integral one at an additive cost of one job per machine.
--
--   Differences from the source:
--   - generalization: related machines, job time x_j/s_i at machine i → unrelated times p_ij ≥ 0; reason: the slot argument is per machine and never uses relatedness; p_ij = x_j/s_i gives the source's statement
--   - encoding: a fractional assignment of processing loads L_i, its positive support, the largest supported job time q_i → fractions y_ij ≥ 0 with Σ_i y_ij = 1, L_i = Σ_j p_ij y_ij, support y_ij > 0, q_i the supremum over the finite set of supported jobs (0 if empty); reason: the proof divides routed volumes by job sizes to get unit mass per original; same instances
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.1, first sentence, p.3

import Mathlib

namespace ReserveLB

/-- **Lemma 2.1, first sentence — whole-job rounding with loads `L_i + q_i`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.1, p.3: "A fractional assignment of processing loads Li can be rounded on its
positive support to whole-job loads at most Li + qi, where qi is the largest supported job time
at i."

For processing times `p_ij ≥ 0` of job `j` on machine `i` and a fractional assignment `y ≥ 0` with
`Σ_i y_ij = 1` for every job, put `L_i = Σ_j p_ij y_ij` and `q_i = max {p_ij : y_ij > 0}`. Then
some whole-job assignment `π` uses only arcs with `y_(π(j) j) > 0` and has load at most
`L_i + q_i` on every machine `i`.

**Formalization Note.** Stated for unrelated times `p_ij`; related machines are `p_ij = x_j/s_i`.
`q_i` is the supremum over the finite set of supported jobs (`0` if there is none). -/
theorem lemma_2_1 {m n : ℕ} (p : Fin m → Fin n → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (y : Fin m → Fin n → ℝ) (hy : ∀ i j, 0 ≤ y i j) (hsum : ∀ j, ∑ i, y i j = 1) :
    ∃ π : Fin n → Fin m, (∀ j, 0 < y (π j) j) ∧
      ∀ i, ∑ j ∈ Finset.univ.filter (fun j => π j = i), p i j ≤
        ∑ j, p i j * y i j + ⨆ j : {j : Fin n // 0 < y i j}, p i j.val := by sorry

end ReserveLB
