-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_lemma_4_2
-- name    : VecKnapsackMitM.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:36:22.970709+00:00
-- url     : https://prove2.me/theorems/d0afd838-dabf-417a-8cfd-06b996e30a43
-- title:
--   Lemma 4.2 — Representative Solutions
-- statement:
--   There are one admissible real-RAM program and one absolute constant $C$ such that for every $d\ge2$, every $I=\{1,\dots,n\}$ of nonnegative items sorted by non-increasing profits and every $0<\varepsilon<1$ (input $R[0]=\varepsilon$, then the items; $N[0]=d$, $N[1]=n$), the program halts within $C\cdot N^d\cdot(\log_2N/\varepsilon)^{C\cdot d}$ steps, $N=\max(n,2)$, with lists $L_1,\dots,L_{n+1}$ of virtual items ($L_i$ at the address in $N[2+i-1]$) such that for every $i\in[n+1]$:
--   * $|L_i|\le N^{d-1}(\log_2N/\varepsilon)^{C\cdot d}$;
--   * every $v\in L_i$ has $\mathrm{set}(v)\subseteq\{i,\dots,n\}$;
--   * $v_\emptyset\in L_i$ (a virtual item representing $\emptyset$);
--   * for every $S\subseteq\{i,\dots,n\}$ some $v\in L_i$ has $\bar w(v)\le\bar w(S)$, $p(v)\ge(1-\varepsilon)p(S)-(d-1+\varepsilon/n)\,p(i)$ and $p(v)\ge\frac{1-\varepsilon}{d}p(S)-\frac{\varepsilon}{n}p(i)$, where $p(n+1)=0$.
--
--   Differences from the source:
--   - encoding: items I = {1, …, n} and dimensions t ∈ {1, …, d} → items Fin n (the paper's item i+1 is i) and dimensions Fin d (the paper's dimension t+1 is t: w̄_1 is t = 0, w̄_d is t = d − 1, the middle dimensions 2, …, d − 1 are 1 ≤ t, t + 2 ≤ d); reason: zero-based finite indexing; same instances and same sets
--   - reading: n inside every bound with a log n factor → N = max(n, 2) (NN n); reason: log 1 = 0 makes the printed bounds 0 at n = 1, contradicting e.g. v_∅ ∈ L_1 (INSIGHTS I1); identical to the printed bound for n ≥ 2
--   - encoding: virtual items (§4.1: v.p, v.w̄, v.item, v.left, v.right) and sets of virtual items → records in memory (R[a] = p, R[a+1+t] = w̄_{t+1}, N[a] = item code, N[a+1], N[a+2] = pointers) checked by IsVItem (decoded set, no cycles, max{2|S|−1, 1} distinct reachable records, stored p and w̄ equal p(S), w̄(S) at every reachable record); a set of virtual items is a stored list (listAt), its length bounding |L|; reason: the paper's own implementation of the interface; p(v), w̄(v) read off the record equal p(set(v)), w̄(set(v))
--   - encoding: output "sets L_1, …, L_{n+1}" → the list L_{k+1} (k : Fin (n+1)) at the address in N[2 + k]; reason: one output cell per list
--   - generalization: an algorithm on the RealRAM (§2, printed p. 8) → an admissible program (VecBalPoly.Admissible: rational literals, no √, no random draws) of the published unit-cost real RAM MatMulTimeLP, which has no floor, no real-to-index conversion and no index multiplication; time = executed instructions including the final halt; reason: fewer primitives only make the existential claim harder; every such program is a deterministic RealRAM algorithm with the same step count, so the Lean statement specializes to the paper's
--   - reading: "in time …^{O(d)}" for given parameters → one program P and one absolute constant C, chosen before d, the error parameters and the input; the O(d) exponent is C·d; reason: the bounds are stated for all d, so the constant in O(d) is absolute; one procedure taking the parameters as input is the stronger of the two readings and is what the paper describes
--   - reading: "in time X" (no explicit O) → at most C·X executed instructions, with the same absolute C as in the exponent; reason: ordinary asymptotic running-time notation permits an absolute leading constant; this does not resolve the separate dimension-uniform base-one issue in INSIGHTS I3, whose printed formulas are retained
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Lemma 4.2, printed pp. 15–16 (PDF 16–17)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_VirtualItem
import Definitions.Def_VecKnapsackMitM_Main_Algorithm3

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-- Bringmann, Kulik, Węgrzycki (2026), Lemma 4.2 (Representative Solutions), printed p. 15
(PDF 16). One admissible program and one constant `C` such that for every `d ≥ 2`, every
`I = {1, …, n}` sorted by non-increasing profits (input `R[0] = ε`, items from `R[1]`;
`N[0] = d`, `N[1] = n`) and every `0 < ε < 1`, the program halts within
`C · N^d · (log₂ N/ε)^{C d}` steps (`N = max(n, 2)`) with lists `L_1, …, L_{n+1}` of virtual items
(the list `L_{k+1}` at the address in `N[2 + k]`) such that for every `k`:
`|L_{k+1}| ≤ N^{d−1} (log₂ N/ε)^{C d}`; every `v ∈ L_{k+1}` has `set(v) ⊆ {k + 1, …, n}`;
`v_∅ ∈ L_{k+1}`; and every `S ⊆ {k + 1, …, n}` has some `v ∈ L_{k+1}` with `w̄(v) ≤ w̄(S)`,
`p(v) ≥ (1 − ε) p(S) − (d − 1 + ε/n) p(k + 1)` and `p(v) ≥ (1 − ε)/d · p(S) − (ε/n) p(k + 1)`,
where `p(n + 1) = 0`. -/
theorem lemma_4_2 :
    ∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ), 2 ≤ d → ∀ I : Items d n, I.Nonneg → I.SortedByProfit →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          RunsWithin P (initState2 (ε :: itemsReals I) [d, n])
            (C * NN n ^ d * (Real.logb 2 (NN n) / ε) ^ (C * (d : ℝ)))
            (fun s => ∀ k : Fin (n + 1),
              ((listAt s (s.N (2 + k.val))).length : ℝ) ≤
                NN n ^ (d - 1) * (Real.logb 2 (NN n) / ε) ^ (C * (d : ℝ)) ∧
              (∀ a ∈ listAt s (s.N (2 + k.val)),
                ∃ S, IsVItem I s a S ∧ S ⊆ Items.suffix n k.val) ∧
              (∃ a ∈ listAt s (s.N (2 + k.val)), IsVItem I s a ∅) ∧
              ∀ S ⊆ Items.suffix n k.val, ∃ a ∈ listAt s (s.N (2 + k.val)), ∃ v,
                IsVItem I s a v ∧ (∀ t, I.weight v t ≤ I.weight S t) ∧
                (1 - ε) * I.profit S - ((d : ℝ) - 1 + ε / n) * pAt I k ≤ I.profit v ∧
                (1 - ε) / d * I.profit S - ε / n * pAt I k ≤ I.profit v) := by sorry

end VecKnapsackMitM.Main
