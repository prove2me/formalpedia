-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_theorem_2_6
-- name    : TurnstileCutSparsify.Main.theorem_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:40:14.775908+00:00
-- url     : https://prove2.me/theorems/90e054c2-03d8-4ff3-9b65-30af8345a667
-- title:
--   Theorem 2.6 — constant-accuracy turnstile sparsifier (24/25, 26/25) in Õ(n) bits, Õ(1) update and Õ(n) recovery time
-- statement:
--   In the stream model ($n\ge2$ vertices, $M$ integer updates of magnitude at most $U$, final weights in $\{0,\dots,U\}$, $M,U\le n^{O(1)}$), for $0<\delta_0<1/4$ with $\delta_0^{-1}\le n^{O(1)}$, there is a one-pass linear sketch that uses $\tilde O(n)$ bits of space, including seeds and recovery workspace, $\tilde O(1)$ worst-case time per update, and $\tilde O(n)$ worst-case recovery time. It always returns a graph with $\tilde O(n)$ edges, and with probability at least $1-\delta_0$ this graph is a positive reweighting $H_0$ of edges of $G$ with
--   $$\tfrac{24}{25}w(S,V\setminus S)\le w_{H_0}(S,V\setminus S)\le\tfrac{26}{25}w(S,V\setminus S)\qquad(S\subseteq V).\qquad(3)$$
--
--   Differences from the source:
--   - generalization: an algorithm that knows n, ε, δ, M and U in advance (§2, p. 9) → one fixed pair of word-RAM programs (upd, rec), chosen before n, ε, δ, M, U; these parameters and the seed reach the machine only through its initial memory; reason: a uniform program is in particular an algorithm for each parameter tuple; the statement is stronger
--   - encoding: word RAM with Θ(log n)-bit words; randomized algorithm; space in bits including seeds and recovery workspace → the published word-RAM core TurnstileRank.TightBounds.RAM; a StreamMachine with word size w (log₂ n ≤ w ≤ C log₂ n), S cells, a seed ρ uniform on Fin K stored in init ρ; space = S·w bits of the whole memory; reason: every stored bit lives in the S cells, so S·w counts seeds, sketch and recovery workspace
--   - encoding: updates (e, Δ); the returned graph H → an update writes min e, max e, Δ (two's complement) into cells 0–2 and runs upd within Tu steps; the output is read after rec halts within Trec steps: cell 0 = number k of entries, entry i = (u, v, p, q) in cells 1+4i … 4+4i, the pair {u, v} with weight p/q; reason: a fixed word-level input/output format; every number is one word
--   - encoding: a turnstile stream of M updates (e, Δ), |Δ| ≤ U, final weights in {0, …, U}, intermediate weights possibly negative → s : List (Update n) with Admissible n M U s: length exactly M, |Δ| ≤ U, net vector in {0, …, U}^N; prefixes may have negative entries; reason: same streams
--   - encoding: "linear sketch" → IsLinearSketch: for every seed ρ there are an integer matrix Φ_ρ with N columns and a map F_ρ with memory after every prefix of every admissible stream = F_ρ(Φ_ρ x), x the prefix's net vector; reason: the BRIEF.json reading of the linear-sketch clause (objects, "one-pass linear-sketch word-RAM algorithm")
--   - encoding: Õ(f) hides polylog(n) factors; n^{O(1)}; O(nε⁻² log² n) → ∀ c : ℕ (M, U, δ⁻¹ ≤ n^c) ∃ C a (Õ(f) = C · f · (log₂ n)^a; O(nε⁻² log² n) = C n ε⁻² (log₂ n)²), with C, a depending only on c; reason: the quantifier order pinned in BRIEF.json objects; log₂ n ≥ 1 since n ≥ 2
--   - encoding: "always returns a graph with Õ(n) edges"; "with probability at least 1 − δ₀ … a positive reweighting H₀ of edges of G with (3)" → on every seed and admissible stream the output decodes to a list with distinct pairs and ≤ C n (log₂ n)^a entries; prob over the seed of: every entry has positive weight on an edge of G, and ApproxCuts (24/25) (26/25) w (outGraph L); reason: same claims
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Theorem 2.6, p. 11

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Theorem 2.6** (Constant-accuracy sparsification; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 11).
In the stream model (`n ≥ 2` vertices, `M` updates of magnitude at most `U`, final weights in
`{0, …, U}`, `M, U ≤ n^{O(1)}`), for `0 < δ₀ < 1/4` with `δ₀⁻¹ ≤ n^{O(1)}`, there is a one-pass
linear sketch that uses `Õ(n)` bits of space, including seeds and recovery workspace, `Õ(1)`
worst-case time per update, and `Õ(n)` worst-case recovery time. It always returns a graph with
`Õ(n)` edges, and with probability at least `1 − δ₀` this graph is a positive reweighting `H₀` of
edges of `G` with `(24/25) w(S, V \ S) ≤ w_{H₀}(S, V \ S) ≤ (26/25) w(S, V \ S)` for all `S ⊆ V` (3).
The machine is the word RAM with `Θ(log n)`-bit words (`log₂ n ≤ w ≤ C log₂ n`); its update and recovery programs are fixed,
and `n, M, U, δ₀` and the seed are in its initial memory. -/
theorem theorem_2_6 :
    ∀ c : ℕ, ∃ (C : ℝ) (a : ℕ) (upd rec : Program),
    ∀ (n M U : ℕ) (δ₀ : ℝ), 2 ≤ n → 1 ≤ U → 0 < δ₀ → δ₀ < 1 / 4 →
      (M : ℝ) ≤ (n : ℝ) ^ c → (U : ℝ) ≤ (n : ℝ) ^ c → δ₀⁻¹ ≤ (n : ℝ) ^ c →
    ∃ (A : StreamMachine) (Tu Trec : ℕ),
      Real.logb 2 n ≤ A.w ∧ (A.w : ℝ) ≤ C * Real.logb 2 n ∧
      ((A.S * A.w : ℕ) : ℝ) ≤ C * n * Real.logb 2 n ^ a ∧
      (Tu : ℝ) ≤ C * Real.logb 2 n ^ a ∧
      (Trec : ℝ) ≤ C * n * Real.logb 2 n ^ a ∧
      WorstCase A upd rec n M U Tu Trec ∧
      (∀ (ρ : Fin A.K) (s : List (Update n)), Admissible n M U s →
        ∃ L, runOutput A upd rec Tu Trec ρ s = some L ∧ (L.map Prod.fst).Nodup ∧
          (L.length : ℝ) ≤ C * n * Real.logb 2 n ^ a) ∧
      ∀ s : List (Update n), Admissible n M U s →
        1 - δ₀ ≤ prob (fun ρ : Fin A.K => ∃ L, runOutput A upd rec Tu Trec ρ s = some L ∧
          (∀ p ∈ L, 0 < p.2 ∧ 0 < finalGraph s p.1) ∧
          ApproxCuts (24 / 25) (26 / 25) (finalGraph s) (outGraph L)) := by sorry

end TurnstileCutSparsify.Main
