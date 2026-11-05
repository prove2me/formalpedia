-- Prove2me | Theorems.Thm_ReusableMatching_lemma_8
-- name    : ReusableMatching.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:49.943709+00:00
-- url     : https://prove2.me/theorems/9bf02e4f-1529-49c6-a8e6-33b1ba92a40b
-- title:
--   Lemma 8 (corrected: part (b) assumes no other seed in period $k(j)-1$ equals $1$): the critical threshold under the regimes of Lemma 7
-- statement:
--   Let an OBMRR instance and $\beta>0$ be given, fix an edge $(i,j)\in E$ and the seeds $Y_{-i,j}$, and let $z_1\le z_2$ in $[0,1]$ split $y^1$ into the three regimes of Lemma 7. Then
--
--   1. for every $y^1\in(z_2,1]$, $\;y^c_j(y^1)=y^c_j(1)$;
--   2. if no resource other than $i$ has seed exactly $1$ in period $k(j)-1$, then for every $y^1\in(z_1,z_2)$, $\;y^c_j(y^1)\le y^c_j(1)$.
--
--   Part 2 bounds the critical threshold in the regime where $i$ is blocked during $p(j)$; Lemma 9 uses it to lower bound $\beta_j$ there. The extra hypothesis of part 2 excludes an event of probability $0$.
--
--   Differences from the source:
--   - correction: Lemma 8(b) for every Y_{−i,j} → Lemma 8(b) under the hypothesis that every resource v ≠ i has seed y_v^{k(j)−1} < 1; reason: false as printed: β = 0.89, d = 3, arrivals 0–3, j = 3; resources i < v and w, weights 1; edges (i,1), (w,1), (i,2), (v,2), (i,3), (v,3); seeds y_w^{k(j)−1} = 0.99, y_v^{k(j)−1} = 1, y_v^{k(j)} = 0. For every y¹ ∈ (0,1), i is matched in period k(j) − 1 and blocked at j, so Lemma 7 holds only with z1 = 0, z2 = 1. In PR(1,1), w takes arrival 1, i beats v at arrival 2 in a tie at reduced price 0, and v is available at j: y^c_j(1) = 0. In PR(0.5,1), i takes arrival 1, v takes arrival 2, and j has no available neighbour: y^c_j(0.5) = 1. The paper's induction (4) fails at the zero-price tie
--   - generalization: z1, z2 are the values constructed in Lemma 7 → any z1 ≤ z2 satisfying the three properties of Lemma 7 (ThreeRegimes); reason: the proof (p.11) uses only Lemma 7(a), 7(b) and Lemma 6; the values of Lemma 7 satisfy the hypothesis
--   - encoding: fixed seeds Y_{−i,j} and the run PR(y¹, y²) (p.9) → a full seed vector Y whose coordinates (i, k(j) − 1) and (i, k(j)) are overwritten by y¹, y² (twoSeed); the statement is for every Y; reason: Lean convention; every Y_{−i,j} is obtained this way, and the paper fixes an arbitrary Y_{−i,j}
--   - encoding: y^c_j(y¹): the solution of r_i(1 − g(y^c)) = max_{v ∈ S_j(y¹,1), (v,j) ∈ E} r_v(1 − g(y_v^{k(j)})), or 0 if there is none (p.9) → sup {y ∈ [0, 1] : M ≤ r_i(1 − g(y))}, which is 0 when the set is empty, with the max over no neighbour equal to 0; reason: for r_i > 0 and β > 0 this is the unique solution when one exists and 0 otherwise; for r_i = 0 every use of y^c carries the factor r_i or compares two thresholds of the same kind
--   - reading: arg max over the available neighbours, no tie rule (Algorithm 1, p.8) → the least maximizer for a linear order on V (a fixed priority order; V and its order are arbitrary); reason: the paper fixes no tie rule; its proofs of Lemmas 4, 6 and 8 compare runs at fixed seeds and need a choice among tied resources that does not depend on the seeds
--   - encoding: arrivals 1, …, |U|; periods of length d with a dummy period before the first arrival (p.8) → arrivals Fin n numbered from 0; arrival t lies in period t / d + 1; period 0 is the dummy period; seeds indexed by V × Fin (n + 1); reason: Lean convention; same instances and same runs
--   - encoding: d ∈ ℕ (p.2) → 1 ≤ d, as a field of the instance; reason: the model ("unavailable for the next d − 1 periods") has no meaning at d = 0
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 8, p.11

import Mathlib
import Definitions.Def_ReusableMatching_ThreeRegimes
import Definitions.Def_ReusableMatching_criticalThreshold

namespace ReusableMatching

/-- **Lemma 8** of Delong, Farhadi, Niazadeh, Sivan & Udwani, arXiv:2110.07084v2, p.11, for a fixed
edge `(i, j) ∈ E`, fixed seeds `Y_{−i,j}` and the values `z1 ≤ z2` of Lemma 7:

"The following statements are true.
a) For every `y¹ ∈ (z2, 1]`, we have `y^c_j(y¹) = y^c_j(1)`.
b) For every `y¹ ∈ (z1, z2)`, we have `y^c_j(y¹) ≤ y^c_j(1)`."

**Corrected:** part (b) is stated under the extra hypothesis that no resource other than `i` has
seed exactly `1` in period `k(j) − 1` (an event of probability `0`). As printed, (b) is false.
Counterexample (`β = 0.89`, `d = 3`, arrivals `0, 1, 2, 3`, `j = 3`, so period `k(j) − 1` holds
the arrivals `0, 1, 2`): resources `i < v` and `w`, all weights `1`, edges `(i,1)`, `(w,1)`,
`(i,2)`, `(v,2)`, `(i,3)`, `(v,3)`; seeds `y_w^{k(j)−1} = 0.99`, `y_v^{k(j)−1} = 1`,
`y_v^{k(j)} = 0`. For every `y¹ ∈ (0, 1)`, `i` is matched in period `k(j) − 1` (to arrival 1 or 2)
and is unavailable at `j`, so Lemma 7 holds only with `z1 = 0`, `z2 = 1`. In `PR(1, 1)`, `w` takes
arrival 1, `i` (reduced price `0`) beats `v` (reduced price `0`) at arrival 2 on the priority
order, and `v` (reduced price `1 − e^{−0.89}`) is available at `j`: `y^c_j(1) = 0`. In
`PR(0.5, 1)`, `i` takes arrival 1, `v` takes arrival 2, and `j` has no available neighbour:
`y^c_j(0.5) = 1 > y^c_j(1)`. The paper's induction (4) fails at the zero-price tie at arrival 2.

**Formalization Note.**
* The hypothesis on `z1 ≤ z2` is Lemma 7's conclusion, `ThreeRegimes I β Y i j z1 z2`, as the
  lemma refers to the values of Lemma 7. Its proof uses only Lemma 7(a), 7(b) and Lemma 6.
* `y^c_j(y¹)` is `criticalThreshold I β Y i j y¹ j`; the statement holds for every seed vector `Y`
  (every `Y_{−i,j}`), and `β > 0` (p.8). -/
theorem lemma_8 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n)
    (z1 z2 : unitInterval) (hz : z1 ≤ z2) (h7 : ThreeRegimes I β Y i j z1 z2) :
    (∀ y1 : unitInterval, z2 < y1 →
      criticalThreshold I β Y i j y1 j = criticalThreshold I β Y i j 1 j) ∧
    ((∀ v : V, v ≠ i → (Y (v, prevPeriod I j) : ℝ) < 1) →
      ∀ y1 : unitInterval, z1 < y1 → y1 < z2 →
        criticalThreshold I β Y i j y1 j ≤ criticalThreshold I β Y i j 1 j) := by sorry

end ReusableMatching
