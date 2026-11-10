-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_lemma_4_8
-- name    : VecKnapsackMitM.Main.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:36:12.182885+00:00
-- url     : https://prove2.me/theorems/f401f910-7b5e-4aa8-9514-7ba8d8d95b23
-- title:
--   Lemma 4.8 — Internal Approximation Lemma
-- statement:
--   There are one admissible real-RAM program and one absolute constant $C$ such that for every $d\ge2$, every sequence $I=\{1,\dots,n\}$ of nonnegative items, weight estimates $\bar W_2,\dots,\bar W_{d-1}\ge0$ and $\varepsilon,\eta\in(0,1]$ (input `sec45Input`), the program halts within $C\cdot N\cdot(\log_2(N/\eta)/\varepsilon)^{C\cdot d}$ steps, $N=\max(n,2)$, with lists $L_1,\dots,L_n$ of virtual items ($L_i$ at the address in $N[2+i-1]$) such that for every $i\in[n]$:
--   * $|L_i|\le(\log_2(N/\eta)/\varepsilon)^{C\cdot d}$;
--   * every $v\in L_i$ has $\mathrm{set}(v)\subseteq\{i,\dots,n\}$;
--   * for every $Q\in\mathcal Q_i:=\{Q\subseteq\{i,\dots,n\}: p(Q)\ge\eta\max_{i\le j\le n}p(j),\ \bar w_t(Q)\le\eta^{-1}\bar W_t\ (2\le t\le d-1)\}$ some $v\in L_i$ has $p(v)\ge(1-\varepsilon)p(Q)$, $\bar w_1(v)\le\max\{(1+\varepsilon)\bar w_1(Q),\eta\max_{i\le j\le n}\bar w_1(j)\}$, $\bar w_d(v)\le\bar w_d(Q)$ and $\bar w_t(v)\le\max\{(1+\varepsilon)\bar w_t(Q),\eta\bar W_t\}$ for $1<t<d$.
--
--   Differences from the source:
--   - encoding: items I = {1, …, n} and dimensions t ∈ {1, …, d} → items Fin n (the paper's item i+1 is i) and dimensions Fin d (the paper's dimension t+1 is t: w̄_1 is t = 0, w̄_d is t = d − 1, the middle dimensions 2, …, d − 1 are 1 ≤ t, t + 2 ≤ d); reason: zero-based finite indexing; same instances and same sets
--   - reading: n inside every bound with a log n factor → N = max(n, 2) (NN n); reason: log 1 = 0 makes the printed bounds 0 at n = 1, contradicting e.g. v_∅ ∈ L_1 (INSIGHTS I1); identical to the printed bound for n ≥ 2
--   - encoding: weight estimates W̄_2, …, W̄_{d−1} ∈ ℝ≥0 → a vector Wt : Fin d → ℝ whose middle coordinates (1 ≤ t, t + 2 ≤ d) are the estimates and are nonnegative; its first and last coordinates are input cells that play no role; reason: uniform input layout; the statement quantifies over every value of the unused coordinates, so it is the same claim
--   - encoding: virtual items (§4.1: v.p, v.w̄, v.item, v.left, v.right) and sets of virtual items → records in memory (R[a] = p, R[a+1+t] = w̄_{t+1}, N[a] = item code, N[a+1], N[a+2] = pointers) checked by IsVItem (decoded set, no cycles, max{2|S|−1, 1} distinct reachable records, stored p and w̄ equal p(S), w̄(S) at every reachable record); a set of virtual items is a stored list (listAt), its length bounding |L|; reason: the paper's own implementation of the interface; p(v), w̄(v) read off the record equal p(set(v)), w̄(set(v))
--   - encoding: output "sets L_1, …, L_n" → the list L_{i+1} (0-based i) at the address in N[2 + i]; reason: one output cell per list
--   - generalization: an algorithm on the RealRAM (§2, printed p. 8) → an admissible program (VecBalPoly.Admissible: rational literals, no √, no random draws) of the published unit-cost real RAM MatMulTimeLP, which has no floor, no real-to-index conversion and no index multiplication; time = executed instructions including the final halt; reason: fewer primitives only make the existential claim harder; every such program is a deterministic RealRAM algorithm with the same step count, so the Lean statement specializes to the paper's
--   - reading: "in time …^{O(d)}" for given parameters → one program P and one absolute constant C, chosen before d, the error parameters and the input; the O(d) exponent is C·d; reason: the bounds are stated for all d, so the constant in O(d) is absolute; one procedure taking the parameters as input is the stronger of the two readings and is what the paper describes
--   - reading: "in time X" (no explicit O) → at most C·X executed instructions, with the same absolute C as in the exponent; reason: ordinary asymptotic running-time notation permits an absolute leading constant; this does not resolve the separate dimension-uniform base-one issue in INSIGHTS I3, whose printed formulas are retained
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Lemma 4.8, printed p. 23 (PDF 24)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_VirtualItem
import Definitions.Def_VecKnapsackMitM_Main_Convolution

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-- Bringmann, Kulik, Węgrzycki (2026), Lemma 4.8 (Internal Approximation Lemma), printed p. 23
(PDF 24). One admissible program and one constant `C` such that for every `d ≥ 2`, every sequence
`I = {1, …, n}` of items, weight estimates `W̄_2, …, W̄_{d−1} ≥ 0` and `ε, η ∈ (0, 1]` (input
`sec45Input`), the program halts within `C · N · (log₂(N/η)/ε)^{C d}` steps (`N = max(n, 2)`) with
lists `L_1, …, L_n` of virtual items (`L_{i+1}` at the address in `N[2 + i]`), each of length at
most `(log₂(N/η)/ε)^{C d}`, every `v ∈ L_{i+1}` with `set(v) ⊆ {i + 1, …, n}`, and for every `i`
and every `Q ⊆ {i + 1, …, n}` with `p(Q) ≥ η · max_{j ≥ i+1} p(j)` and `w̄_t(Q) ≤ η^{−1} W̄_t`
(`2 ≤ t ≤ d − 1`) some `v ∈ L_{i+1}` with `p(v) ≥ (1 − ε) p(Q)`,
`w̄₁(v) ≤ max{(1 + ε) w̄₁(Q), η · max_{j ≥ i+1} w̄₁(j)}`, `w̄_d(v) ≤ w̄_d(Q)` and
`w̄_t(v) ≤ max{(1 + ε) w̄_t(Q), η W̄_t}` for `1 < t < d`. -/
theorem lemma_4_8 :
    ∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ), 2 ≤ d → ∀ I : Items d n, I.Nonneg →
        ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
        ∀ (ε η : ℝ), 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
          RunsWithin P (sec45Input I Wt ε η)
            (C * NN n * (Real.logb 2 (NN n / η) / ε) ^ (C * (d : ℝ)))
            (fun s => ∀ i : Fin n,
              ((listAt s (s.N (2 + i.val))).length : ℝ) ≤
                (Real.logb 2 (NN n / η) / ε) ^ (C * (d : ℝ)) ∧
              (∀ a ∈ listAt s (s.N (2 + i.val)),
                ∃ S, IsVItem I s a S ∧ S ⊆ Items.suffix n i.val) ∧
              ∀ Q ⊆ Items.suffix n i.val,
                η * Items.maxOver (Items.suffix n i.val) I.p ≤ I.profit Q →
                (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → I.weight Q t ≤ Wt t / η) →
                ∃ a ∈ listAt s (s.N (2 + i.val)), ∃ v, IsVItem I s a v ∧
                  (1 - ε) * I.profit Q ≤ I.profit v ∧
                  (∀ t : Fin d, t.val = 0 → I.weight v t ≤
                    max ((1 + ε) * I.weight Q t)
                      (η * Items.maxOver (Items.suffix n i.val) I.w1)) ∧
                  (∀ t : Fin d, t.val + 1 = d → I.weight v t ≤ I.weight Q t) ∧
                  ∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d →
                    I.weight v t ≤ max ((1 + ε) * I.weight Q t) (η * Wt t)) := by sorry

end VecKnapsackMitM.Main
