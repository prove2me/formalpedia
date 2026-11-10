-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_theorem_6_1
-- name    : TurnstileRank.TightBounds.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:09:09.823025+00:00
-- url     : https://prove2.me/theorems/6546d856-0ec0-449e-bfe7-5bb0c45844a2
-- title:
--   Theorem 6.1 — turnstile algorithms on polynomial-length streams become O(S)-space linear sketches ([JLY26])
-- statement:
--   Theorem 6.1 ([JLY26, Corollary 6.1.7(2) and Remark 6.2.5]). Let X ⊆ Z^N be a finite set of vectors of Euclidean norm at most D, let R ⊆ X × O be a relation, let 0 < δ < 1, and let R ≥ max{N⁸, D³, δ⁻³} be a sufficiently large integer. Suppose an S-bit randomized algorithm, on every unit-update turnstile stream of length at most R⁴ whose final vector y lies in X, outputs o with (y, o) ∈ R with probability at least 1 − δ. Then there is a randomized linear sketch of space O(S), with an absolute constant, that outputs such an o with probability at least 1 − 3δ for every y ∈ X. The same holds for algorithms promised strict-turnstile streams, when X consists of nonnegative vectors.
--
--   In Lean: there are $C>0$ and $R_0$ such that for every $N$, every finite $X\subseteq\mathbb Z^N$ of Euclidean norm at most $D$, every output type $O$ and relation $\mathrm{Rel}\subseteq\mathbb Z^N\times O$, every $0<\delta<1$, every integer $R\ge\max\{R_0,N^8,D^3,\delta^{-3}\}$, and every randomized turnstile algorithm (published `BoolCSPDel.TurnstileAlg (Fin N) Ω St O`, finite state set $St$, seed probability measure $\mu$): (i) if on every unit-update stream of length at most $R^4$ whose final vector $y$ lies in $X$ the output satisfies $\mathrm{Rel}(y,\cdot)$ with probability at least $1-\delta$, then there is a linear sketch $L$ on $[N]$ (query type `Unit`, answers in $O$) with `HasSpace L (C · log₂|St|)` whose output satisfies $\mathrm{Rel}(y,\cdot)$ with probability at least $1-3\delta$ for every $y\in X$; (ii) the same when $X$ consists of nonnegative vectors and the hypothesis is only on strict-turnstile streams (`BoolCSPDel.IsLegal`).
--
--   Differences from the source:
--   - encoding: "a randomized linear sketch of space O(S), with an absolute constant"; "a sufficiently large integer R" → `HasSpace L (C * memoryBits St)` with C > 0, and R ≥ R₀, with C and R₀ absolute, quantified before N, X, D, δ and the algorithm; reason: O(·)/Ω(·) with an absolute constant uniform over all parameters, made explicit and quantified before them
--   - encoding: an S-bit randomized algorithm → the published `BoolCSPDel.TurnstileAlg` with a finite state set `St`, S = `CosDensity.memoryBits St` = log₂|St|, seed from any probability space; success via `CosDensity.SucceedsWP`; reason: the paper's streaming model (p. 11, §6) with the seed free
--   - encoding: a randomized linear sketch that outputs o → `LinearSketch N Ρ G Unit O` (Definition 3.1 with the single query `()`); reason: there is one query
--   - encoding: Euclidean norm → `Real.sqrt (Σ_i y_i²)`; reason: definition
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - encoding: a finite set X of integer vectors and a relation on X × O → a Finset X and a predicate Rel on all integer vectors, evaluated only for y ∈ X; reason: every relation on X extends outside X arbitrarily; no extra instances are tested
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Theorem 6.1, printed p. 28 (PDF 29)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_LinearSketch

open scoped BigOperators
open MeasureTheory

namespace TurnstileRank.TightBounds

/-- Theorem 6.1 ([JLY26, Corollary 6.1.7(2) and Remark 6.2.5]), as stated in the paper: an `S`-bit
randomized algorithm that, on every unit-update turnstile stream of length at most `R⁴` whose final
vector lies in a finite `X ⊆ ℤ^N` of Euclidean norm at most `D`, outputs `o` with `(y, o) ∈ Rel` with
probability at least `1 − δ`, where `R ≥ max{R₀, N⁸, D³, δ⁻³}`, yields a randomized linear sketch of
space `O(S)` that outputs such an `o` with probability at least `1 − 3δ` for every `y ∈ X`; and the
same for algorithms promised strict-turnstile streams when `X` consists of nonnegative vectors. -/
theorem theorem_6_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ R0 : ℕ,
      ∀ (N : ℕ) (X : Finset (Fin N → ℤ)) (D : ℝ),
        (∀ y ∈ X, Real.sqrt (∑ i, ((y i : ℤ) : ℝ) ^ 2) ≤ D) →
      ∀ (O : Type) (Rel : (Fin N → ℤ) → O → Prop) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ R : ℕ, R0 ≤ R → (N : ℝ) ^ 8 ≤ R → D ^ 3 ≤ R → δ⁻¹ ^ 3 ≤ R →
      ∀ (Ω St : Type) [MeasurableSpace Ω] [Fintype St] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : BoolCSPDel.TurnstileAlg (Fin N) Ω St O),
        ((∀ s : List (Fin N × Bool), s.length ≤ R ^ 4 → (fun i => BoolCSPDel.freq s i) ∈ X →
            CosDensity.SucceedsWP μ
              (fun ω => Rel (fun i => BoolCSPDel.freq s i) (A.out ω (A.run ω s)))
              (ENNReal.ofReal (1 - δ))) →
          ∃ (Ρ G : Type) (_ : AddCommGroup G) (L : LinearSketch N Ρ G Unit O),
            L.HasSpace (C * CosDensity.memoryBits St) ∧
            ∀ y ∈ X, 1 - 3 * δ ≤ prob L.law {ρ | Rel y (L.dec ρ (L.state ρ y) ())}) ∧
        ((∀ y ∈ X, ∀ i, 0 ≤ y i) →
          (∀ s : List (Fin N × Bool), BoolCSPDel.IsLegal s → s.length ≤ R ^ 4 →
            (fun i => BoolCSPDel.freq s i) ∈ X →
            CosDensity.SucceedsWP μ
              (fun ω => Rel (fun i => BoolCSPDel.freq s i) (A.out ω (A.run ω s)))
              (ENNReal.ofReal (1 - δ))) →
          ∃ (Ρ G : Type) (_ : AddCommGroup G) (L : LinearSketch N Ρ G Unit O),
            L.HasSpace (C * CosDensity.memoryBits St) ∧
            ∀ y ∈ X, 1 - 3 * δ ≤ prob L.law {ρ | Rel y (L.dec ρ (L.state ρ y) ())}) := by sorry

end TurnstileRank.TightBounds
