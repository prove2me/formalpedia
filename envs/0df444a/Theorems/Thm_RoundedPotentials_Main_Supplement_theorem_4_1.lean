-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_theorem_4_1
-- name    : RoundedPotentials.Main.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:07:50.694201+00:00
-- url     : https://prove2.me/theorems/b0720490-2d0c-4cf6-8ece-5222ddb1554f
-- title:
--   Theorem 4.1 — Exact maximum-flow value in annotated streams (Theorem 1.3)
-- statement:
--   Fix $c>0$. Consider a turnstile stream of integer capacity updates $(u,v,\Delta)$, $u\ne v$, for a directed network on $[n]$, $n\ge2$, with specified terminals $s\ne t$. The stream is promised to have final capacities in $\{0,\dots,W\}$, $W\ge1$.
--
--   There is a constant $C$ depending only on $c$, and for every $n,W,s,t$ an online annotation scheme, whose help follows the stream, with the following properties.
--
--   1. **Perfect completeness.** For every stream there is a help string of at most $Cn(\lfloor\log_2(nW)\rfloor+1)$ bits such that the verifier outputs the true value $\mathrm{MaxFlow}(s,t)$ for every choice of coins.
--   2. **Soundness.** For every stream and every help string, which may depend on the stream but not on the coins, the probability that the verifier outputs a wrong value is at most $n^{-c}$.
--   3. **Space.** The verifier's memory, including the coins it keeps and the memory used while reading the help, never exceeds $Cn(\lfloor\log_2(nW)\rfloor+1)$ bits.
--
--   For polynomially bounded $W$, the total cost is therefore $\widetilde O(n)$. Together with Corollary 4.3 this gives Theorem 1.3, answering Thaler's question about annotation schemes of total cost $o(n^2)$.
--
--   **Formalization Note** The model is `AnnotationScheme`: a bit-string memory with arbitrary transitions. The help is processed one bit at a time after the stream, and the coins enter only through the initial memory.
--
--   Differences from the source:
--   - encoding: online annotation scheme with private randomness; help and space costs in bits → AnnotationScheme: bit-string memory, arbitrary (non-uniform) transitions, coins only through the initial memory, help read bit by bit after the stream, one scheme per public (n, W, s, t); reason: the cost model of [CCMT14, CGT20], which charges help and memory bits; all annotation follows the stream, as the theorem states
--   - encoding: updates of a directed network → updates on ordered pairs of distinct vertices; reason: §2 graphs are loopless
--   - encoding: O_c(n log(nW)) bits → C·n·(⌊log₂(nW)⌋+1) with C depending only on c; reason: explicit form of the O-bound
--   - reading: "For polynomially bounded W, its total cost is Õ(n)" → not a separate conjunct; reason: for W ≤ n^D the bound C·n·(⌊log₂(nW)⌋+1) on help and on space is at most C(D+2)·n·(⌊log₂ n⌋+1), an arithmetic consequence for the same scheme
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 19, Theorem 4.1

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Streaming

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main

theorem theorem_4_1 (c : ℝ) (hc : 0 < c) : ∃ C : ℕ,
    ∀ (n W : ℕ), 2 ≤ n → 1 ≤ W → ∀ (s t : Fin n), s ≠ t →
      ∃ S : AnnotationScheme n,
        -- perfect completeness, with help of `O_c(n log(nW))` bits
        (∀ σ : List (Update n), TurnstilePromise W σ →
          ∃ h : List Bool, h.length ≤ C * n * (Nat.log 2 (n * W) + 1) ∧
            ∀ r : Fin S.coinBits → Bool, ∃ v : ℕ, S.result r σ h = some v ∧
              MatrixMaxValue n W (streamCap σ) s t v) ∧
        -- soundness error at most `n^{-c}` against every help string fixed before the coins
        (∀ σ : List (Update n), TurnstilePromise W σ → ∀ h : List Bool,
          S.prob (fun r => ∃ v : ℕ, S.result r σ h = some v ∧
              ¬ MatrixMaxValue n W (streamCap σ) s t v) ≤ (n : ℝ) ^ (-c)) ∧
        -- space `O_c(n log(nW))` bits, including while reading the help
        (∀ σ : List (Update n), TurnstilePromise W σ → ∀ (h : List Bool)
          (r : Fin S.coinBits → Bool), ∀ mem ∈ S.memories r σ h,
            mem.length ≤ C * n * (Nat.log 2 (n * W) + 1)) := by sorry

end RoundedPotentials.Main.Supplement
