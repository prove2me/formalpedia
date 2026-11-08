-- Prove2me | Theorems.Thm_StreamColour_theorem_5_26
-- name    : StreamColour.theorem_5_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:55.783785+00:00
-- url     : https://prove2.me/theorems/1919497a-f1bf-4e9c-88a6-83c228b9b53c
-- title:
--   Theorem 5.26 — Algorithm B: one pass, $\tilde O(nh)$ bits, failure $6n^{-10}$, for $\Delta>C_*h^2$
-- statement:
--   For all sufficiently large $C$, and then all sufficiently large $C_*$, there is a one-pass randomized program with the following guarantees. For all $1\le k<\Delta\le n-1$ with $\Delta>C_*h^2$, every $n$-vertex graph $G$ of maximum degree at most $\Delta$ with a proper $(\Delta-k)$-colouring, and every order of its edges:
--
--   1. on every execution, the program uses at most $A\,n\,h\,\ell^B$ bits, including all postprocessing workspace;
--   2. it outputs a proper $(\Delta-k)$-colouring with probability at least $1-6n^{-10}$.
--
--   This is the branch of the main theorem for $\Delta>C_*h^2$.
--
--   Differences from the source:
--   - reading: "Then Algorithm B" → some program; Algorithm B (p.75) is not a Lean object; reason: as for Theorem 4.1: the goal needs only existence, and the paper's proof constructs such a program
--   - reading: "a randomized algorithm", with no machine named → a `DynBrooks.Program` (finite instruction list, memory $\mathbb N\to\{0,1\}^w$, read-once input, write-only output, coin words) of word size $w=c_w\ell(n)$, fixed before $n$; reason: a finite-state model with an arbitrary output map would make the workspace clause empty, and every step of the paper's pseudo-code runs here
--   - encoding: $\tilde O(nh)$ bits on every execution, including postprocessing workspace → $A\,n\,h\,\ell(n)^B$ bits, as `w * written.card`, for all $\omega,t$, with $P,c_w,A,B$ after $C,C_*$ and before $n,\Delta,k$; reason: $\tilde O$ suppresses factors polynomial in $\log(n+1)$ (§3, p.20); cells ever written are the workspace, for all coin tapes and all times, including runs that never halt; output words are write-only and not charged
--   - encoding: an insertion-only stream, parameters known, labels in $[n]$ → the input list $[n,\Delta,k]$, then labels in $1..n$ of each edge once, in either orientation, then the sentinel $0$; reason: the number of edges is not given, and $0$ is not a label
--   - encoding: "outputs a proper colouring" → the program halts with a list of length $n$ whose entries lie in $1..q$ and differ across every edge; reason: reporting failure, or never halting, is not an output of a colouring
--   - encoding: "with probability at least $c$" → a measurable event of measure at least $c$ inside the success set, under independent uniform coin words; reason: the inner bound avoids overstating an event by outer measure; uniform samples come by rejection sampling, exact almost surely
--   - reading: "For sufficiently large fixed constants" → $\exists C_0,\forall C\ge C_0,\exists C_{*,0},\forall C_*\ge C_{*,0}$; reason: the order of §6: $C_*$ is chosen after $C$
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Theorem 5.26, p.84 (PDF 86)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_StreamModel

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Theorem 5.26, p.84 (PDF 86).

**Formalization Note.** "Sufficiently large fixed constants" is `∃ C₀, ∀ C ≥ C₀, ∃ Cs₀, ∀ Cs ≥ Cs₀`, in §6's order: `C_∗` after `C`. Then `P, cw, A, B` before `n, ∆, k, G, es`. Space on every `ω` and `t`, with no promise
of halting. `Õ(nh)` is `A n h ℓ(n)^B`. Failure exactly `6 n⁻¹⁰`. Algorithm B (p.75) is not a Lean object: the statement is about the program that exists. "At most one pass" is the type of `read`. -/
theorem theorem_5_26 : ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ Cs₀ : ℝ, ∀ Cs ≥ Cs₀,
    ∃ (P : DynBrooks.Program) (cw A B : ℕ),
    ∀ (n Δ k : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)),
    1 ≤ k → k < Δ → Δ ≤ n - 1 → (∀ v, (G.neighborSet v).ncard ≤ Δ) → G.Colorable (Δ - k) →
    IsEdgeStream G es → Cs * (hParam C n k : ℝ) ^ 2 < (Δ : ℝ) →
    let w := cw * ell n
    let c₀ := initConfig w (streamInput Δ k es)
    (∀ (ω : ℕ → BitVec w) (t : ℕ),
      spaceBits w (DynBrooks.run P ω c₀ t) ≤ A * n * hParam C n k * ell n ^ B) ∧
    ProbAtLeast (DynBrooks.coinMeasure w) {ω | OutputsColouring P ω c₀ (Δ - k) G}
      (ENNReal.ofReal (1 - 6 / (n : ℝ) ^ 10)) := by sorry

end StreamColour
