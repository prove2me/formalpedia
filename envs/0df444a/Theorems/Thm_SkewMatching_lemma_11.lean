-- Prove2me | Theorems.Thm_SkewMatching_lemma_11
-- name    : SkewMatching.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:54.520835+00:00
-- url     : https://prove2.me/theorems/de9d4ef2-52fe-4e57-92e1-374f93592d39
-- title:
--   Lemma 11 — an integral symmetric flow of value at least K/2 in n^{2+o(1)} time with high probability
-- statement:
--   There is one program $P$ and one function $g(n)\to 0$ such that for every $C>0$ there is a constant $K_0>0$ with the following property. For every simple skew-symmetric graph $G$ on $N$ vertices, source $s$, integer $K\ge 1$ such that $G$ has an integral symmetric flow of value at least $K$, and listing of the edges of $G$, the probability that $P$ fails to halt within
--
--   $$
--   \lceil K_0(N+2)^{2+g(N+2)}\rceil
--   $$
--
--   steps with the output encoding an integral symmetric flow of value at least $K/2$ is at most $(N+2)^{-C}$.
--
--   Note that the time does not depend on $K$. This is the core of the algorithm, one round of the proof of Theorem 2.
--
--   Differences from the source:
--   - reading: we can compute → a Machine.Program, a unit-cost word RAM with coins and word bound (n+2)^wordExp; reason: the paper names no machine
--   - reading: n^{2+o(1)} time with high probability → ∃ g → 0 before C, a constant after C, failure probability (N+2)^{−C} for arbitrary C; reason: the paper gives no order; this is the stronger one
--   - encoding: a parameter K → K a natural number with K ≥ 1; reason: K = 2^i in the proof of Theorem 2
--   - encoding: n → N+2 in the time and the failure probability; reason: N = 0, 1 would otherwise be vacuous or junk; implies the printed form for N ≥ 2 up to the constant
--   - reading: simple: no parallel edges between any two vertices → Simple: (tail, head) is injective, so antiparallel pairs and loops are allowed; reason: the wording of p.1 read per ordered pair; §2.3 says the algorithm also handles a constant number of parallel edges, and loops carry only cycle flow
--   - encoding: a skew-symmetric graph with unit capacity → a simple SkewGraph, input as flowMem; reason: all graphs in the paper are simple and of unit capacity (§2.3, p.4); the paper fixes no input format
--   - encoding: finds an integral symmetric flow of value at least K/2 → when halted, memory cell −1 holds ℓ and cells −2−2j, −3−2j hold the tail and head of the j-th of the ℓ edges with flow 1, each edge once (DecodesFlow); reason: the paper fixes no output format; for a Simple graph the ends determine the edge
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 11, p.5

import Mathlib
import Definitions.Def_SkewMatching_DecodesFlow

namespace SkewMatching

open Filter Topology

/-- **Lemma 11**, p.5. "There exists an algorithm that, given a skew-symmetric graph G with unit capacity and a parameter K, assuming that the maximum integral symmetric flow of G is at least K, finds an integral symmetric flow of value at least K/2 in n^{2+o(1)} time with high probability."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 11, p.5.

**Formalization Note.** One program and one `g → 0` before every `C > 0`, then the time constant `K₀` (named so to keep it apart from the paper's parameter `K`), then the instance. `Simple` is the standing assumption of §2.3, p.4. The bad event has outer measure at most `(N+2)^{−C}`; `N + 2` keeps `N = 0, 1` from being vacuous. Machine and
layout: `Machine.Program` with `W = (N+2)^wordExp`, `flowMem`, `DecodesFlow`. -/
theorem lemma_11 :
    ∃ (P : Machine.Program) (g : ℕ → ℝ), Tendsto g atTop (𝓝 0) ∧
      ∀ C : ℝ, 0 < C → ∃ K₀ : ℝ, 0 < K₀ ∧
        ∀ (N : ℕ) {E : Type} [Fintype E] (G : SkewGraph (Fin N) E), G.Simple →
          ∀ (s : Fin N) (K : ℕ) (el : List E), 1 ≤ K → IsFullListing el →
            (∃ f, G.IsFlow s f ∧ (K : ℤ) ≤ G.value s f) →
            let W := Machine.wordBound P (N + 2)
            let σ₀ := Machine.initState (flowMem G s K el)
            Machine.coinTape {τ | ¬ ∃ T ≤ ⌈K₀ * ((N : ℝ) + 2) ^ (2 + g (N + 2))⌉₊,
                Machine.HaltsWithin P W τ σ₀ T ∧
                  ∃ f, G.IsFlow s f ∧ (K : ℤ) ≤ 2 * G.value s f ∧
                    DecodesFlow G (Machine.run P W τ σ₀ T).mem f} ≤
              ENNReal.ofReal (((N : ℝ) + 2) ^ (-C)) := by sorry

end SkewMatching
