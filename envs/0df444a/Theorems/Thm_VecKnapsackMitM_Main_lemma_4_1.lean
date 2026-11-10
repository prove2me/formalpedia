-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_lemma_4_1
-- name    : VecKnapsackMitM.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:34:21.410202+00:00
-- url     : https://prove2.me/theorems/59f2d11b-592c-4312-a9aa-50990d6369a1
-- title:
--   Lemma 4.1 — Approximation Lemma (instances with slack by convolution)
-- statement:
--   There are one admissible real-RAM program and one absolute constant $C$ such that for every $d\ge2$, every set $I$ of $n$ nonnegative items, weight estimates $\bar W_2,\dots,\bar W_{d-1}\ge0$, profit estimate $\tilde p\ge0$ and $\varepsilon,\eta\in(0,1]$ (input $R[0]=\varepsilon$, $R[1]=\eta$, $R[2]=\tilde p$, $R[3+t]=$ `Wt t`, then the items; $N[0]=d$, $N[1]=n$), the program halts within $C\cdot N\cdot(\log_2(N/\eta)/\varepsilon)^{C\cdot d}$ steps, $N=\max(n,2)$, with a list $L$ of virtual items (address in $N[2]$), each with $\mathrm{set}(v)\subseteq I$, such that every $Q\in\mathcal Q:=\{Q\subseteq I: p(Q)\ge\eta\tilde p,\ \bar w_t(Q)\le\eta^{-1}\bar W_t\ (2\le t\le d-1)\}$ has some $v\in L$ with
--   $p(v)\ge\min\{(1-\varepsilon)p(Q),\eta^{-1}\tilde p\}$, $\bar w_1(v)\le(1+\varepsilon)\bar w_1(Q)$, $\bar w_d(v)\le\bar w_d(Q)$ and $\bar w_t(v)\le\max\{(1+\varepsilon)\bar w_t(Q),\eta\bar W_t\}$ for $1<t<d$.
--
--   Differences from the source:
--   - encoding: items I = {1, …, n} and dimensions t ∈ {1, …, d} → items Fin n (the paper's item i+1 is i) and dimensions Fin d (the paper's dimension t+1 is t: w̄_1 is t = 0, w̄_d is t = d − 1, the middle dimensions 2, …, d − 1 are 1 ≤ t, t + 2 ≤ d); reason: zero-based finite indexing; same instances and same sets
--   - reading: n inside every bound with a log n factor → N = max(n, 2) (NN n); reason: log 1 = 0 makes the printed bounds 0 at n = 1, contradicting e.g. v_∅ ∈ L_1 (INSIGHTS I1); identical to the printed bound for n ≥ 2
--   - encoding: weight estimates W̄_2, …, W̄_{d−1} ∈ ℝ≥0 → a vector Wt : Fin d → ℝ whose middle coordinates (1 ≤ t, t + 2 ≤ d) are the estimates and are nonnegative; its first and last coordinates are input cells that play no role; reason: uniform input layout; the statement quantifies over every value of the unused coordinates, so it is the same claim
--   - encoding: virtual items (§4.1: v.p, v.w̄, v.item, v.left, v.right) and sets of virtual items → records in memory (R[a] = p, R[a+1+t] = w̄_{t+1}, N[a] = item code, N[a+1], N[a+2] = pointers) checked by IsVItem (decoded set, no cycles, max{2|S|−1, 1} distinct reachable records, stored p and w̄ equal p(S), w̄(S) at every reachable record); a set of virtual items is a stored list (listAt), its length bounding |L|; reason: the paper's own implementation of the interface; p(v), w̄(v) read off the record equal p(set(v)), w̄(set(v))
--   - generalization: an algorithm on the RealRAM (§2, printed p. 8) → an admissible program (VecBalPoly.Admissible: rational literals, no √, no random draws) of the published unit-cost real RAM MatMulTimeLP, which has no floor, no real-to-index conversion and no index multiplication; time = executed instructions including the final halt; reason: fewer primitives only make the existential claim harder; every such program is a deterministic RealRAM algorithm with the same step count, so the Lean statement specializes to the paper's
--   - reading: "in time …^{O(d)}" for given parameters → one program P and one absolute constant C, chosen before d, the error parameters and the input; the O(d) exponent is C·d; reason: the bounds are stated for all d, so the constant in O(d) is absolute; one procedure taking the parameters as input is the stronger of the two readings and is what the paper describes
--   - reading: "in time X" (no explicit O) → at most C·X executed instructions, with the same absolute C as in the exponent; reason: ordinary asymptotic running-time notation permits an absolute leading constant; this does not resolve the separate dimension-uniform base-one issue in INSIGHTS I3, whose printed formulas are retained
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Lemma 4.1, printed p. 15 (PDF 16)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_VirtualItem

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-- Bringmann, Kulik, Węgrzycki (2026), Lemma 4.1 (Approximation Lemma), printed p. 15
(PDF 16). One admissible program and one constant `C` such that for every `d ≥ 2`, every set of
`n` items, weight estimates `W̄_2, …, W̄_{d−1} ≥ 0`, profit estimate `p̃ ≥ 0` and
`ε, η ∈ (0, 1]` (input `R[0] = ε`, `R[1] = η`, `R[2] = p̃`, `R[3 + t] = Wt t`, then the items;
`N[0] = d`, `N[1] = n`), the program halts within `C · N · (log₂(N/η)/ε)^{C d}` steps
(`N = max(n, 2)`) with a list `L` of virtual items (at the address in `N[2]`) such that every
`Q ⊆ I` with `p(Q) ≥ η p̃` and `w̄_t(Q) ≤ η^{−1} W̄_t` (`2 ≤ t ≤ d − 1`) has some `v ∈ L` with
`p(v) ≥ min{(1 − ε) p(Q), η^{−1} p̃}`, `w̄₁(v) ≤ (1 + ε) w̄₁(Q)`, `w̄_d(v) ≤ w̄_d(Q)` and
`w̄_t(v) ≤ max{(1 + ε) w̄_t(Q), η W̄_t}` for `1 < t < d`. -/
theorem lemma_4_1 :
    ∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ), 2 ≤ d → ∀ I : Items d n, I.Nonneg →
        ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
        ∀ (pt ε η : ℝ), 0 ≤ pt → 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
          RunsWithin P (initState2 ([ε, η, pt] ++ finVec Wt ++ itemsReals I) [d, n])
            (C * NN n * (Real.logb 2 (NN n / η) / ε) ^ (C * (d : ℝ)))
            (fun s => (∀ a ∈ listAt s (s.N 2), ∃ S, IsVItem I s a S) ∧
              ∀ Q : Finset (Fin n), η * pt ≤ I.profit Q →
                (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → I.weight Q t ≤ Wt t / η) →
                ∃ a ∈ listAt s (s.N 2), ∃ v, IsVItem I s a v ∧
                  min ((1 - ε) * I.profit Q) (pt / η) ≤ I.profit v ∧
                  (∀ t : Fin d, t.val = 0 → I.weight v t ≤ (1 + ε) * I.weight Q t) ∧
                  (∀ t : Fin d, t.val + 1 = d → I.weight v t ≤ I.weight Q t) ∧
                  ∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d →
                    I.weight v t ≤ max ((1 + ε) * I.weight Q t) (η * Wt t)) := by sorry

end VecKnapsackMitM.Main
