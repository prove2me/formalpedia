-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_theorem_1_1
-- name    : TurnstileCutSparsify.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:40:24.040202+00:00
-- url     : https://prove2.me/theorems/f57597fd-e538-4b38-9580-ef4181b9f444
-- title:
--   Theorem 1.1 — a one-pass linear-sketch (1±ε)-cut sparsifier of a weighted turnstile stream in Õ(n/ε²) bits, Õ(1) update time and Õ(n/ε²) recovery time, with O(nε⁻² log² n) edges
-- statement:
--   The input is a weighted graph $G=(V,E,w)$ on $n\ge2$ vertices, given by a turnstile stream of $M$ integer edge-weight updates of magnitude at most $U$, with final weights in $\{0,1,\dots,U\}$; running times refer to the word RAM with $\Theta(\log n)$-bit words.
--
--   **Theorem 1.1.** Let $0<\varepsilon<1$ and $0<\delta<1/4$, and assume $M,U,\delta^{-1}\le n^{O(1)}$. There is a one-pass linear-sketch algorithm using $\tilde O(n/\varepsilon^2)$ bits of space, $\tilde O(1)$ worst-case time per update, and $\tilde O(n/\varepsilon^2)$ worst-case recovery time that, with probability at least $1-\delta$, returns a positive reweighting $H$ of $O(n\varepsilon^{-2}\log^2n)$ edges of $G$ such that
--   $$(1-\varepsilon)\,w(S,V\setminus S)\le w_H(S,V\setminus S)\le(1+\varepsilon)\,w(S,V\setminus S)\quad\text{for every }S\subseteq V.$$
--
--   Formally: for every $c$ there are $C,a$ and fixed update and recovery programs such that for all $n\ge2$, $\varepsilon\in(0,1)$, $\delta\in(0,1/4)$, $M,U,\delta^{-1}\le n^c$ there is a streaming machine with $\log_2n\le w\le C\log_2n$, $S\cdot w\le C(n/\varepsilon^2)\log_2^an$, update time $\le C\log_2^an$, recovery time $\le C(n/\varepsilon^2)\log_2^an$, the linear-sketch clause, and, for every admissible stream, probability at least $1-\delta$ over the seed that the output lists distinct edges of $G$ with positive weights, at most $Cn\varepsilon^{-2}\log_2^2n$ of them, forming a $(1\pm\varepsilon)$-cut sparsifier of $G$. There is no hypothesis on Theorem 2.7 or Proposition 2.8: both are separate items of this mission.
--
--   Differences from the source:
--   - generalization: an algorithm that knows n, ε, δ, M and U in advance (§2, p. 9) → one fixed pair of word-RAM programs (upd, rec), chosen before n, ε, δ, M, U; these parameters and the seed reach the machine only through its initial memory; reason: a uniform program is in particular an algorithm for each parameter tuple; the statement is stronger
--   - encoding: word RAM with Θ(log n)-bit words; randomized algorithm; space in bits including seeds and recovery workspace → the published word-RAM core TurnstileRank.TightBounds.RAM; a StreamMachine with word size w (log₂ n ≤ w ≤ C log₂ n), S cells, a seed ρ uniform on Fin K stored in init ρ; space = S·w bits of the whole memory; reason: every stored bit lives in the S cells, so S·w counts seeds, sketch and recovery workspace
--   - encoding: updates (e, Δ); the returned graph H → an update writes min e, max e, Δ (two's complement) into cells 0–2 and runs upd within Tu steps; the output is read after rec halts within Trec steps: cell 0 = number k of entries, entry i = (u, v, p, q) in cells 1+4i … 4+4i, the pair {u, v} with weight p/q; reason: a fixed word-level input/output format; every number is one word
--   - encoding: a turnstile stream of M updates (e, Δ), |Δ| ≤ U, final weights in {0, …, U}, intermediate weights possibly negative → s : List (Update n) with Admissible n M U s: length exactly M, |Δ| ≤ U, net vector in {0, …, U}^N; prefixes may have negative entries; reason: same streams
--   - encoding: "linear sketch" → IsLinearSketch: for every seed ρ there are an integer matrix Φ_ρ with N columns and a map F_ρ with memory after every prefix of every admissible stream = F_ρ(Φ_ρ x), x the prefix's net vector; reason: the BRIEF.json reading of the linear-sketch clause (objects, "one-pass linear-sketch word-RAM algorithm")
--   - encoding: Õ(f) hides polylog(n) factors; n^{O(1)}; O(nε⁻² log² n) → ∀ c : ℕ (M, U, δ⁻¹ ≤ n^c) ∃ C a (Õ(f) = C · f · (log₂ n)^a; O(nε⁻² log² n) = C n ε⁻² (log₂ n)²), with C, a depending only on c; reason: the quantifier order pinned in BRIEF.json objects; log₂ n ≥ 1 since n ≥ 2
--   - encoding: "returns a positive reweighting H of O(nε⁻² log² n) edges of G" with the cut bounds → GoodOutput (finalGraph s) (1 − ε) (1 + ε) (C n ε⁻² (log₂ n)²) L: distinct pairs, positive rational weights on edges of G, at most C n ε⁻² (log₂ n)² entries, ApproxCuts for every S ⊆ V; reason: same claim
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Theorem 1.1, p. 2

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Theorem 1.1** (Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 2).
Let `0 < ε < 1` and `0 < δ < 1/4`, and assume `M, U, δ⁻¹ ≤ n^{O(1)}`. There is a one-pass
linear-sketch algorithm using `Õ(n/ε²)` bits of space, `Õ(1)` worst-case time per update, and
`Õ(n/ε²)` worst-case recovery time that, with probability at least `1 − δ`, returns a positive
reweighting `H` of `O(nε⁻² log² n)` edges of `G` such that
`(1 − ε) w(S, V \ S) ≤ w_H(S, V \ S) ≤ (1 + ε) w(S, V \ S)` for every `S ⊆ V`.

The input is a turnstile stream of `M` integer updates of magnitude at most `U` on `n ≥ 2` vertices
with final weights in `{0, …, U}`; the machine is the word RAM with `Θ(log n)`-bit words (`log₂ n ≤ w ≤ C log₂ n`), the
space `S · w` counts every stored bit (seed, sketch, recovery workspace), and the update and
recovery programs are fixed, with `n, ε, δ, M, U` and the seed in the initial memory. -/
theorem theorem_1_1 :
    ∀ c : ℕ, ∃ (C : ℝ) (a : ℕ) (upd rec : Program),
    ∀ (n M U : ℕ) (ε δ : ℝ), 2 ≤ n → 1 ≤ U → 0 < ε → ε < 1 → 0 < δ → δ < 1 / 4 →
      (M : ℝ) ≤ (n : ℝ) ^ c → (U : ℝ) ≤ (n : ℝ) ^ c → δ⁻¹ ≤ (n : ℝ) ^ c →
    ∃ (A : StreamMachine) (Tu Trec : ℕ),
      Real.logb 2 n ≤ A.w ∧ (A.w : ℝ) ≤ C * Real.logb 2 n ∧
      ((A.S * A.w : ℕ) : ℝ) ≤ C * (n / ε ^ 2) * Real.logb 2 n ^ a ∧
      (Tu : ℝ) ≤ C * Real.logb 2 n ^ a ∧
      (Trec : ℝ) ≤ C * (n / ε ^ 2) * Real.logb 2 n ^ a ∧
      WorstCase A upd rec n M U Tu Trec ∧
      ∀ s : List (Update n), Admissible n M U s →
        1 - δ ≤ prob (fun ρ : Fin A.K => ∃ L, runOutput A upd rec Tu Trec ρ s = some L ∧
          GoodOutput (finalGraph s) (1 - ε) (1 + ε) (C * n * ε⁻¹ ^ 2 * Real.logb 2 n ^ 2) L) := by sorry

end TurnstileCutSparsify.Main
