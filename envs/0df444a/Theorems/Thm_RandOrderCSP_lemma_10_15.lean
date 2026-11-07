-- Prove2me | Theorems.Thm_RandOrderCSP_lemma_10_15
-- name    : RandOrderCSP.lemma_10_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:08.880224+00:00
-- url     : https://prove2.me/theorems/29ae12d0-3cc0-4d23-83c7-c24db73a7cf7
-- title:
--   Lemma 10.15 — random-order estimator for random exploration types
-- statement:
--   For every $k\ge2$, $R\ge1$, finite color set $\Gamma$ and $\varepsilon>0$ there is a randomized one-pass streaming algorithm with the following guarantee. Given a nonempty $\Gamma$-colored $k$-uniform hypergraph $\Phi=(H,f)$ on $[n]$ in uniformly random order, it outputs $\hat p\in\mathbb R^{\mathcal E_{R,\Gamma}}$ such that, with $\eta_n=(\log(n+2))^{-1/(2k^R+2)}$,
--
--   $$\mathbb P_\pi\Big[\mathbb P_{\text{internal}}\big[\|\hat p-\text{Rand-Exp-Type}_R(\Phi)\|_1\le\varepsilon\mid\pi\big]\ge\tfrac23\Big]\ge1-\eta_n.$$
--
--   The algorithm uses $O_{k,R,|\Gamma|,\varepsilon}(\log^3(n+m+2))$ bits of space, on a stream of $m$ updates, and it depends on $n$ but not on $m$.
--
--   Together with Lemmas 10.5 and 10.14 this gives the algorithm of the mission's goal.
--
--   Differences from the source:
--   - reading: O(log³(n + m + 2)) bits of space, with m unknown to the algorithm → on every coin outcome and every stream l, the state has length at most C·(log₂(n + |l| + 2))³; reason: the fixed-s model of §3.5 cannot express growing space; this is the literal worst-case reading, and the printed algorithm stores bounded data with counters at most m
--   - encoding: a randomized algorithm as a distribution over deterministic algorithms → a probability space (Ω, μ) and a map from Ω to deterministic algorithms; reason: coins along an unbounded stream need a non-atomic distribution, which PMF does not reach
--   - encoding: P_internal[‖p̂ − p‖₁ ≤ ε | π] ≥ 2/3 → μ{ω : ‖p̂ − p‖₁ > ε} ≤ 1/3 as an outer measure; reason: equivalent for measurable events; the outer-measure form assumes no measurability
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Lemma 10.15, p.55

import Mathlib
import Definitions.Def_RandOrderCSP_ExpTree
import Definitions.Def_RandOrderCSP_VarAlg
import Definitions.Def_RandOrderCSP_StreamAlg

open MeasureTheory

namespace RandOrderCSP

/-- **Lemma 10.15 (random-order estimator for random exploration types).** Singer, Tulsiani, Velusamy, *A
dichotomy theorem for approximating CSPs in random-order streams*, STOC 2027 submission (manuscript
sha256 3aca9d2f…), Lemma 10.15, p.55.

**Formalization Note.** The internal randomness is a probability space `(Ω, μ)` with `A n ω` a
deterministic variable-state algorithm; since the algorithm draws fresh coins along an unbounded stream,
it is a non-atomic distribution over deterministic algorithms, and `PMF` would not reach it. The algorithm
sees `n` but not `m`. Space: on **every** coin outcome and **every** stream `l` of `|l|` updates, the state
has length at most `C·(log₂(n+|l|+2))³`, which is the reading "`O(log³(n+m+2))` bits on a stream of length
`m`". The inner bound `P_internal[‖p̂ − p‖₁ ≤ ε | π] ≥ 2/3` is the outer-measure bound
`μ{ω : ‖p̂ − p‖₁ > ε} ≤ 1/3`, which carries no measurability assumption. `log` is base two (p.10). The
ℓ¹ norm is unnormalized (p.10) and the `tsum` is a finite sum (`ℰ_{R,Col}` is finite). -/
theorem lemma_10_15 {k R : ℕ} (hk : 2 ≤ k) (hR : 1 ≤ R) (Col : Type) [Finite Col] (ε : ℝ) (hε : 0 < ε) :
    ∃ (C : ℝ) (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (A : (n : ℕ) → Ω → VarAlg (ColoredEdge k Col n) (expTypes k R Col → ℝ)),
      (∀ n ω (l : List (ColoredEdge k Col n)),
        (((A n ω).run l).length : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + l.length + 2) ^ 3) ∧
      ∀ (n m : ℕ), 1 ≤ m → ∀ Φ : Fin m → ColoredEdge k Col n,
        1 - Real.logb 2 ((n : ℝ) + 2) ^ (-(1 / (2 * (k : ℝ) ^ R + 2))) ≤
          (Nat.card {π : Equiv.Perm (Fin m) //
              μ {ω | ε < ∑' τ, |(A n ω).answer (streamOf Φ π) τ -
                  expTypeLaw (edgesHG Φ) (fun j => (Φ j).2) R τ|} ≤ ENNReal.ofReal (1 / 3)} : ℝ) /
            (Nat.card (Equiv.Perm (Fin m)) : ℝ) := by sorry

end RandOrderCSP
