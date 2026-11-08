-- Prove2me | Theorems.Thm_StreamColour_theorem_4_1
-- name    : StreamColour.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:55.035295+00:00
-- url     : https://prove2.me/theorems/a70e9ac5-fafc-42a7-9765-159a3e1ef2c6
-- title:
--   Theorem 4.1 — Algorithm A: one pass, $\tilde O(nh+n\Delta/h)$ bits, failure $n^{-10}$
-- statement:
--   For every sufficiently large $C$, with $h=\lceil C(k+\ell^{10})\rceil$, there is a one-pass randomized program with the following guarantees. For all $1\le k<\Delta\le n-1$, every $n$-vertex graph $G$ of maximum degree at most $\Delta$ with a proper $(\Delta-k)$-colouring, and every order of its edges:
--
--   1. on every execution, the program uses at most $A\,n\,(h+\Delta/h)\,\ell^B$ bits, including postprocessing workspace;
--   2. it outputs a proper $(\Delta-k)$-colouring with probability at least $1-n^{-10}$;
--   3. for every constant $C_*\ge0$, if $\Delta\le C_*h^2$ it uses at most $A(1+C_*)\,n\,h\,\ell^B$ bits on every execution.
--
--   This is the branch of the main theorem for $\Delta\le C_*h^2$.
--
--   Differences from the source:
--   - reading: "Algorithm A has the following guarantees" → some program has them; Algorithm A (pp.46–47) is not a Lean object; reason: the pseudo-code is too long to transcribe within a statement and the goal needs only existence; the paper's proof constructs such a program
--   - reading: "a randomized algorithm", with no machine named → a `DynBrooks.Program` (finite instruction list, memory $\mathbb N\to\{0,1\}^w$, read-once input, write-only output, coin words) of word size $w=c_w\ell(n)$, fixed before $n$; reason: a finite-state model with an arbitrary output map would make the workspace clause empty, and every step of the paper's pseudo-code runs here
--   - encoding: $\tilde O(nh+n\Delta/h)$ bits on every execution, including postprocessing workspace → $A\,n\,(h+\Delta/h)\,\ell(n)^B$ bits, as `w * written.card`, for all $\omega,t$, with $P,c_w,A,B$ after $C$ and before $n,\Delta,k$; reason: $\tilde O$ suppresses factors polynomial in $\log(n+1)$ (§3, p.20); cells ever written are the workspace, for all coin tapes and all times, including runs that never halt; output words are write-only and not charged
--   - encoding: an insertion-only stream, parameters known, labels in $[n]$ → the input list $[n,\Delta,k]$, then labels in $1..n$ of each edge once, in either orientation, then the sentinel $0$; reason: the number of edges is not given, and $0$ is not a label
--   - encoding: "outputs a proper colouring" → the program halts with a list of length $n$ whose entries lie in $1..q$ and differ across every edge; reason: reporting failure, or never halting, is not an output of a colouring
--   - encoding: "with probability at least $c$" → a measurable event of measure at least $c$ inside the success set, under independent uniform coin words; reason: the inner bound avoids overstating an event by outer measure; uniform samples come by rejection sampling, exact almost surely
--   - encoding: "its space is $\tilde O(nh)$ when $\Delta\le C_*h^2$, for any fixed $C_*$" → $A(1+C_*)\,n\,h\,\ell^B$ for every real $C_*\ge0$; reason: the constant is explicit: $nh+n\Delta/h\le(1+C_*)nh$ as on p.85
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Theorem 4.1, p.23 (PDF 25)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_StreamModel

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Theorem 4.1, p.23 (PDF 25).

**Formalization Note.** One pass is the type of `read`; the input model is `streamInput`; the space bound holds for all `ω`
and `t`, with no promise of halting. `Õ(f)` is `A · f · ℓ(n)^B`, and `P, cw, A, B` are chosen after `C` and before `n, ∆, k`.
"In particular" has its constant explicit: for every `C_∗ ≥ 0` and `∆ ≤ C_∗h²`, the space is at most `A (1 + C_∗) n h ℓ^B`.
Algorithm A itself (pp.46–47) is not a Lean object: the statement is about the program that exists. -/
theorem theorem_4_1 : ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ (P : DynBrooks.Program) (cw A B : ℕ),
    ∀ (n Δ k : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)),
    1 ≤ k → k < Δ → Δ ≤ n - 1 → (∀ v, (G.neighborSet v).ncard ≤ Δ) → G.Colorable (Δ - k) →
    IsEdgeStream G es →
    let h : ℝ := (hParam C n k : ℝ)
    let w := cw * ell n
    let c₀ := initConfig w (streamInput Δ k es)
    (∀ (ω : ℕ → BitVec w) (t : ℕ),
      (spaceBits w (DynBrooks.run P ω c₀ t) : ℝ) ≤
        (A : ℝ) * (n : ℝ) * (h + (Δ : ℝ) / h) * (ell n : ℝ) ^ B) ∧
    ProbAtLeast (DynBrooks.coinMeasure w) {ω | OutputsColouring P ω c₀ (Δ - k) G}
      (ENNReal.ofReal (1 - 1 / (n : ℝ) ^ 10)) ∧
    ∀ Cs : ℝ, 0 ≤ Cs → (Δ : ℝ) ≤ Cs * h ^ 2 → ∀ (ω : ℕ → BitVec w) (t : ℕ),
      (spaceBits w (DynBrooks.run P ω c₀ t) : ℝ) ≤
        (A : ℝ) * (1 + Cs) * (n : ℝ) * h * (ell n : ℝ) ^ B := by sorry

end StreamColour
