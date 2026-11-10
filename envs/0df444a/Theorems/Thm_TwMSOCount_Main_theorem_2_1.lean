-- Prove2me | Theorems.Thm_TwMSOCount_Main_theorem_2_1
-- name    : TwMSOCount.Main.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:47:34.924244+00:00
-- url     : https://prove2.me/theorems/026725d8-cc12-4d85-9a56-edf514b9513d
-- title:
--   Theorem 2.1 — one uniform algorithm computes $Z_{k,n}(\psi)$ with $f(\theta)O(n)$ entries, $f(\theta)O(n^2)$ operations, $f(\theta)\mathrm{poly}(n,L)$ bits, and supports an exact sampler
-- statement:
--   Let $C = \{0,\dots,r-1\}$ ($r\ge1$), let $\psi$ be an MSO2 sentence over the incidence vocabulary $V_C$, let $\lambda_c, \beta_{c,d}=\beta_{d,c}$ be nonnegative rationals, and let
--   $$Z_{k,n}(\psi) = \sum_{\substack{V(G)=[n],\ \chi:[n]\to C\\ \mathrm{tw}(G)\le k,\ (G,\chi)\models\psi}} \prod_{v}\lambda_{\chi(v)}\prod_{\{a,b\}\in E(G)}\beta_{\chi(a),\chi(b)} .$$
--   Write $\theta = (k, C, \psi)$, $|\theta| = k + r + \mathrm{size}(\psi)$, and $L$ for the total bit length of the weights.
--
--   **Theorem.** There are two programs $P$ and $Q$ of the rational-cell RAM, a computable $f:\mathbb N\to\mathbb N$ and a constant $c$, all fixed before the input, such that for every $n, k \in \mathbb N$, every $r\ge1$, every sentence $\psi$ and all weights, the run of $P$ on the input $(n,k,r,\psi,\lambda,\beta)$ halts with output $Z_{k,n}(\psi)$, and for $n\ge1$
--   $$\#\text{scalar entries}\le f(|\theta|)\,n,\quad \#\text{arithmetic operations}\le f(|\theta|)\,n^2,\quad \text{bit time},\ \text{bit space}\le f(|\theta|)\,(n+L)^c .$$
--   Moreover, if $Z_{k,n}(\psi)>0$, a call of $Q$ started from the final memory of that run (the tables) with a fresh fair-coin tape halts almost surely and outputs the code of each colored graph $(G,\chi)$ on $[n]$ with $\mathrm{tw}(G)\le k$ and $(G,\chi)\models\psi$ with probability exactly
--   $$\frac{W(G,\chi)}{Z_{k,n}(\psi)},$$
--   and for $n\ge1$ its expected bit time is at most $f(|\theta|)(n+L)^c$.
--
--   This is the main result of the paper: fixed-parameter exact weighted counting and exact sampling of labeled graphs of bounded treewidth with an MSO2 property, with the number of stored values linear and the number of arithmetic operations quadratic in $n$. Corollary 1.1 (all graphs of treewidth at most $k$, uniformly) is the case of one color, unit weights and $\psi = \top$.
--
--   **Formalization Note.** The program is quantified before $n, k, r, \psi$ and the weights; $f$ is applied to $|\theta|$. One call of $Q$ is one sample; repeated samples are repeated calls from the same tables with independent tapes.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling i ↦ i−1 changes no instance
--   - encoding: f(θ) for a computable f of θ = (k, C, ψ) → f (thetaSize k ψ) with f : ℕ → ℕ Computable and thetaSize = k + r + size ψ; reason: finitely many θ have a given size, so the two forms are interchangeable
--   - encoding: f(θ)O(n), f(θ)O(n²), f(θ) poly(n, L) → ≤ f·n, ≤ f·n², ≤ f·(n+L)^c with one computable f and one exponent c; reason: constant factors are absorbed into f; every polynomial in n, L is at most a constant times (n+L)^c when n+L ≥ 1
--   - encoding: a uniform algorithm in the cost model of Definition D.1 (bit-cost RAM or multitape TM, equivalent up to polynomial factors) → a fixed program of a log-cost RAM with rational cells (`Program`, `runStats`); reason: Definition D.1 allows a bit-cost RAM; charging (ℓ₁+ℓ₂+1)² per arithmetic step on reduced fractions is polynomially equivalent to Turing-machine bit operations
--   - reading: arithmetic operations (+, −, ×, ÷, comparison of stored rationals) and scalar entries (stored values) → every executed add/sub/mul/div/floor/comparison instruction, index arithmetic included; scalar entries = cells ever written, input cells included; reason: the source fixes no machine; counting every arithmetic instruction and every written cell can only make the bounds harder
--   - encoding: inputs n, k, C, ψ and the weights; L = total binary length of the weights → encodeInput: one stored rational per number (n in binary), ψ by its prefix code, λ and the full r×r matrix β; weightLength sums the bit lengths of these r + r² entries; reason: the r² entries of β have at most twice the length of its independent entries, so L changes by a factor ≤ 2
--   - encoding: C a nonempty finite color set; nonnegative rational weights, β symmetric → C = Fin r with 0 < r; Weights r with ℚ≥0 entries and a symmetry field; reason: same instances up to naming the colors
--   - encoding: the tables support a sampler outputting each (G, χ) with probability W/Z, in expected time per sample → a program Q started from the final configuration of P (Config.restart keeps every cell) on the fair-coin tape coinTape; output law via callOutput, halting almost surely, expected callCost; reason: one call is one sample; the tables are reused unchanged
--   - encoding: expected bit time per sample (expectation over the fair bits) → Measurable (callCost Q …) ∧ ∫⁻ callCost ∂coinTape ≤ bound; reason: ∫⁻ is a lower integral; measurability (true for every program, as the cost depends on a finite prefix of coins) makes it the expectation
--   - encoding: MSO2 sentence over V_C = {Vertex, Edge, Inc} ∪ {P_c} → Formula r Empty with IsSentence; Vertex and Edge are expressed by the sorts; reason: sorted MSO2 has the same expressive power
--   - encoding: the counting algorithm constructs tables supporting sampling → StoresTables in the final memory: each existing entry of size at most n has a distinct written cell containing its recurrence value; reason: the final memory must contain completed numerical tables, rather than merely an unspecified auxiliary word
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Theorem 2.1, p. 4 (PDF 5)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_TwMSOCount_Main_Tables

open MeasureTheory
open scoped ENNReal

namespace TwMSOCount.Main

theorem theorem_2_1 :
    ∃ (P Q : Program) (f : ℕ → ℕ) (c : ℕ), Computable f ∧
      ∀ (n k r : ℕ) (hr : 0 < r), ∀ (ψ : Formula r Empty), ψ.IsSentence → ∀ (w : Weights r),
        letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
        ∃ s : RunStats,
          runStats P zeroTape (Config.init (encodeInput n k r ψ w)) = some s ∧
          s.final.output = [((Z k n r ψ w : ℚ≥0) : ℚ)] ∧
          (∃ SM : StateMap r k, SM.IsStateMap ψ ∧ StoresTables SM w n s.final) ∧
          (1 ≤ n →
            s.entries ≤ f (thetaSize k ψ) * n ∧
            s.arith ≤ f (thetaSize k ψ) * n ^ 2 ∧
            s.time ≤ f (thetaSize k ψ) * (n + weightLength w) ^ c ∧
            s.space ≤ f (thetaSize k ψ) * (n + weightLength w) ^ c) ∧
          (0 < Z k n r ψ w →
            coinTape {τ | callOutput Q s.final.restart τ = none} = 0 ∧
            Measurable (callCost Q s.final.restart) ∧
            (∀ (G : SimpleGraph (Fin n)) (χ : Fin n → Fin r),
              PlantedSubgraphLD.tw G ≤ k → ModelsPsi G χ ψ →
              coinTape {τ | callOutput Q s.final.restart τ = some (codeGraph G χ)} =
                ENNReal.ofReal (((w.W G χ / Z k n r ψ w : ℚ≥0) : ℚ) : ℝ)) ∧
            (1 ≤ n →
              ∫⁻ τ, callCost Q s.final.restart τ ∂coinTape ≤
                ((f (thetaSize k ψ) * (n + weightLength w) ^ c : ℕ) : ℝ≥0∞))) := by sorry

end TwMSOCount.Main
