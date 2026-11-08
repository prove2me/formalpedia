-- Prove2me | Theorems.Thm_StreamColour_theorem_1_1
-- name    : StreamColour.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:58.342237+00:00
-- url     : https://prove2.me/theorems/da0dd923-4d48-459b-87a2-d68b0e04365d
-- title:
--   Theorem 1.1 — one pass and $\tilde O(nk)$ bits find a proper $(\Delta-k)$-colouring, with failure $6n^{-10}$
-- statement:
--   There is a single randomized one-pass streaming program, with word size $c_w\ell(n)$ and constants $A,B$, with the following guarantees. Let $1\le k<\Delta\le n-1$, and suppose an $n$-vertex simple graph $G$ has maximum degree at most $\Delta$ and admits a proper $(\Delta-k)$-colouring. For every order of the distinct edges of $G$:
--
--   1. the program makes one insertion-only pass over the edges;
--   2. it outputs a proper $(\Delta-k)$-colouring with probability at least $1-6n^{-10}$;
--   3. it uses at most
--   $$A\,n\,k\,\ell(n)^B$$
--   bits on every execution, including postprocessing workspace, where $\ell(n)=\max\{1,\lceil\log_2(n+1)\rceil\}$.
--
--   The parameters $n,\Delta,k$ are known before the stream, and the graph and edge order are fixed independently of the algorithm's randomness. Postprocessing time is unrestricted. This answers a question of Flin and Halldórsson, and it is optimal up to polylogarithmic factors for $k<(\Delta-1)/2$ by their lower bound.
--
--   Differences from the source:
--   - reading: "a randomized algorithm", with no machine named → a `DynBrooks.Program` (finite instruction list, memory $\mathbb N\to\{0,1\}^w$, read-once input, write-only output, coin words) of word size $w=c_w\ell(n)$, fixed before $n$; reason: a finite-state model with an arbitrary output map would make the workspace clause empty, and every step of the paper's pseudo-code runs here
--   - encoding: $\tilde O(nk)$ bits on every execution, including postprocessing workspace → $A\,n\,k\,\ell(n)^B$ bits, as `w * written.card`, for all $\omega,t$, with $P,c_w,A,B$ before $n,\Delta,k,G$, and the edge list; reason: $\tilde O$ suppresses factors polynomial in $\log(n+1)$ (§3, p.20); cells ever written are the workspace, for all coin tapes and all times, including runs that never halt; output words are write-only and not charged
--   - encoding: an insertion-only stream, parameters known, labels in $[n]$ → the input list $[n,\Delta,k]$, then labels in $1..n$ of each edge once, in either orientation, then the sentinel $0$; reason: the number of edges is not given, and $0$ is not a label
--   - encoding: "outputs a proper colouring" → the program halts with a list of length $n$ whose entries lie in $1..q$ and differ across every edge; reason: reporting failure, or never halting, is not an output of a colouring
--   - encoding: "with probability at least $c$" → a measurable event of measure at least $c$ inside the success set, under independent uniform coin words; reason: the inner bound avoids overstating an event by outer measure; uniform samples come by rejection sampling, exact almost surely
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Theorem 1.1, p.2 (PDF 4); §3, p.20 (PDF 22)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_StreamModel

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Theorem 1.1, p.2 (PDF 4), with the model of §3, p.20 (PDF 22).

For `1 ≤ k < ∆ ≤ n − 1`, an `n`-vertex graph of maximum degree at most `∆` that admits a proper `(∆ − k)`-colouring is coloured by one randomized program that reads the distinct edges once, uses `Õ(nk)` bits on every
execution including postprocessing workspace, and outputs a proper `(∆ − k)`-colouring with probability at least `1 − 6n⁻¹⁰`.

**Formalization Note.** The paper names no machine. A program is a `DynBrooks.Program`, of word size `cw · ℓ(n)`. One pass is the type of `read`. Space is `w` bits per cell ever written, for **all** `ω` and `t`, including runs that never halt. `Õ(nk)` is
`A · n · k · ℓ(n)^B`, and `P, cw, A, B` come **before** `n, ∆, k, G, es`: any later, and storing the whole graph would qualify, or the finite control could hide workspace. "Known before the stream" is the head of `streamInput`; "the graph and edge order are fixed independently of the randomness" is `∀ G es` before
`coinMeasure`; "time unrestricted" is `∃ t`. Maximum degree is an upper bound, not an equality. -/
theorem theorem_1_1 : ∃ (P : DynBrooks.Program) (cw A B : ℕ),
    ∀ (n Δ k : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)),
    1 ≤ k → k < Δ → Δ ≤ n - 1 → (∀ v, (G.neighborSet v).ncard ≤ Δ) → G.Colorable (Δ - k) →
    IsEdgeStream G es →
    let w := cw * ell n
    let c₀ := initConfig w (streamInput Δ k es)
    (∀ (ω : ℕ → BitVec w) (t : ℕ),
      spaceBits w (DynBrooks.run P ω c₀ t) ≤ A * n * k * ell n ^ B) ∧
    ProbAtLeast (DynBrooks.coinMeasure w) {ω | OutputsColouring P ω c₀ (Δ - k) G}
      (ENNReal.ofReal (1 - 6 / (n : ℝ) ^ 10)) := by sorry

end StreamColour
