-- Prove2me | Theorems.Thm_SamplingLLL_Supplement_theorem_2_13
-- name    : SamplingLLL.Supplement.theorem_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:56:53.696966+00:00
-- url     : https://prove2.me/theorems/1cd55729-5d27-4796-9cc6-316d92162343
-- title:
--   Theorem 2.13, p.9 — independent transversals: FPRAS and perfect sampler for blocks of size $\ge9\Delta$, product weights, bipartite hosts
-- statement:
--   Let $J=(V,E)$ be a graph of maximum degree $\Delta\ge1$ whose vertex set is partitioned into blocks $V_1,\dots,V_n$, with $b_{\min}$ and $b_{\max}$ the smallest and largest block sizes. There are absolute constants $C$, $d$, $K$ such that the following hold for the sampler and FPRAS of Appendix B.
--
--   1. **(i) Uniform law.** If every block has size at least $9\Delta$: there is an independent transversal; the sampler terminates almost surely and its law is uniform on the independent transversals; it makes at most
--   $$
--   C\,|E|\,(b_{\max}/b_{\min})^2
--   $$
--   recursive invocations in expectation, at expected bit cost at most $C(|E|+1)(b_{\max}/b_{\min})^2(L+1)^d$; and for every rational $\varepsilon\in(0,1]$ the counter outputs the number of independent transversals within relative error $\varepsilon$ with probability at least $3/4$, in at most $C((L+\ell(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$ bit operations.
--   2. **(ii) Product weights.** If every block carries a rational probability distribution $\pi_i$ with $\max_{v\in V_i}\pi_i(v)\le(9\Delta)^{-1}$ and one vertex is selected from each block independently: the probability $Z_\pi$ that the selection is an independent transversal is positive; the sampler's law is that of the selection conditioned on being independent, in expected time $C(L+1)^d$; and the FPRAS approximates $Z_\pi$ within relative error $\varepsilon$ with probability at least $3/4$, in at most $C((L+\ell(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$ bit operations.
--   3. **(iii) Bipartite hosts.** If $J$ is bipartite with sides $\mathrm A$ and $\mathrm B$, every block lies within one side, and $\Delta_{\mathrm A},\Delta_{\mathrm B}\ge1$ bound the degrees of the vertices on the two sides, the conclusions of (ii) hold when $\max_v\pi_i(v)\le(9\Delta_{\mathrm B})^{-1}$ for every block on side $\mathrm A$ and $\max_v\pi_i(v)\le(9\Delta_{\mathrm A})^{-1}$ for every block on side $\mathrm B$.
--
--   Here $L$ is the input length. The result gives counting and exact sampling of independent transversals at block size $9\Delta$.
--
--   **Formalization Note** Blocks are $V_i=\{0,\dots,b_i\}$ and the instance is `Blocks`; the procedures are `Blocks.itSampler`, `Blocks.itFpras`, `Blocks.itCount`. The algorithm first deletes the edges inside a block and the edges of zero product mass and runs with the maximum degree of the remaining graph (per side in (iii)), which does not exceed the given bound. A recursive frame is one invocation of an insertion kernel, a deletion kernel or a reciprocal coin.
--
--   Differences from the source:
--   - reading: "has an FPRAS", "has an expected-polynomial-time perfect sampler" → the clauses are stated for the explicit procedures `itSampler`, `itFpras`, `itCount` of Appendix B, with no existential quantifier over programs; reason: the base mission's `Proc` has no machine model, so an existential over programs would make every running-time clause vacuous; this is the convention of the published Theorem 2.6
--   - encoding: a partition of $V$ into blocks $V_1,\dots,V_n$ → $V$ is the disjoint union of the sets $\{0,\dots,b_i\}$; reason: every partition into nonempty blocks has this form after relabelling; same instances
--   - reading: "$O(|E|(b_{\max}/b_{\min})^2)$ expected recursive frames, each of expected polynomial bit cost" → expected calls at most $C|E|(b_{\max}/b_{\min})^2$ and expected ticks at most $C(|E|+1)(b_{\max}/b_{\min})^2(L+1)^d$, with $C$, $d$ absolute; reason: the per-frame cost is stated as the total cost bound, the product of the frame bound and a polynomial; the $+1$ covers the initial draw when $E=\emptyset$
--   - reading: "has an FPRAS" with universal polynomial degree → for every rational $\varepsilon\in(0,1]$: termination, relative error $\varepsilon$ with probability at least $3/4$, worst-case cost at most $C((L+\ell(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$ under the work cap of p.25; reason: the standard meaning, with the success probability and cap of the proof (p.25) and the bit length of the rational $\varepsilon$ in the input
--   - encoding: the uniform law on independent transversals and the conditioned selection are assumed to exist → existence of an independent transversal in (i) and $Z_\pi>0$ in (ii), (iii) are stated conclusions; reason: the conditional laws require them, and the proof establishes them
--   - encoding: in (iii), "$J$ is bipartite with sides A and B, every block lies within one side" → a map from block indices to the two sides such that every edge of $J$ joins vertices of blocks on different sides; reason: a side for every block is the same datum as a bipartition of $V$ that is constant on blocks; same instances
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.13 and Definition 2.12, p.9; proof in Appendix B.1–B.4 (pp.25–30), B.7 (pp.32–33), B.8 (pp.33–34)

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_itData

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc Blocks

/-- Theorem 2.13 (Independent transversals), p.9, all three parts. Let `J` be a graph of maximum degree
`∆ ≥ 1` on the disjoint union of blocks `V_1, …, V_n`.

(i) If every block has size at least `9∆`: there are independent transversals; the sampler of Appendix B
terminates almost surely with the uniform law on them, makes at most `C |E| (b_max/b_min)²` expected
recursive invocations (frames), and has expected bit cost at most `C (|E|+1) (b_max/b_min)² (L+1)^d`, that is
polynomial per frame; and the counting FPRAS, for every rational `ε ∈ (0,1]`, approximates the number of
independent transversals within relative error `ε` with probability at least `3/4`, in worst-case time
`C ((L + bits ε + 1) ⌈1/ε⌉)^d`.

(ii) If every block carries a rational distribution `π_i` with `max_v π_i(v) ≤ (9∆)^{-1}`: the probability
`Z_π` that the independent `π`-selection is an independent transversal is positive; the sampler has the law
of the selection conditioned on independence, in expected time `C (L+1)^d`; and the FPRAS approximates `Z_π`
as in (i).

(iii) If `J` is bipartite with sides `A`, `B` (`side i = true` is side `A`), every block on one side, and
`∆_A, ∆_B ≥ 1` bound the degrees on the two sides: the conclusions of (ii) hold when `max π_i ≤ (9∆_B)^{-1}`
on every block of side `A` and `max π_i ≤ (9∆_A)^{-1}` on every block of side `B`.

The constants `C`, `d`, `K` are absolute: `d` is the universal polynomial degree.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.13, p.9; proof in
Appendix B.1–B.4 (pp.25–30), B.7 (pp.32–33), B.8 (pp.33–34).

**Formalization Note.** The clauses are about the explicit procedures of Appendix B (`itSampler`,
`itFpras`, `itCount` over `itData`), not about programs chosen by `∃`. Block `V_i` is `Fin (b i + 1)`. The
algorithm deletes edges inside a block and edges of zero product mass, and runs with the maximum degree
`∆` (in (iii): `∆_X` per side) of the remaining graph, at least `1`; these are valid choices of the degree
bounds, since they do not exceed the given ones. A frame is one invocation of an insertion kernel, a
deletion kernel or a reciprocal coin, the base `expCalls`. `L = itInputSize`. -/
theorem theorem_2_13 : ∃ C d K : ℕ,
    -- (i) uniform law
    (∀ {n : ℕ} (b : Fin n → ℕ) (J : SimpleGraph (uniform b).Vtx) [DecidableRel J.Adj],
      1 ≤ J.maxDegree → (∀ i, 9 * J.maxDegree ≤ b i + 1) →
      let W := uniform b
      let bmax : ℕ := Finset.univ.fold max 0 fun i => b i + 1
      let bmin : ℕ := Finset.univ.fold min bmax fun i => b i + 1
      let E : ℕ := J.edgeFinset.card
      0 < W.numIT J ∧
      mass (W.itSampler J (W.DeltaAll J)) = 1 ∧
      (∀ y, law (W.itSampler J (W.DeltaAll J)) y =
        if W.IsIT J y then ((W.numIT J : ℝ≥0∞))⁻¹ else 0) ∧
      expCalls (W.itSampler J (W.DeltaAll J)) ≤
        ENNReal.ofReal ((C : ℝ) * E * ((bmax : ℝ) / bmin) ^ 2) ∧
      expTicks (W.itSampler J (W.DeltaAll J)) ≤
        ENNReal.ofReal ((C : ℝ) * (E + 1) * ((bmax : ℝ) / bmin) ^ 2 *
          ((W.itInputSize J : ℝ) + 1) ^ d) ∧
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
        mass (W.itCount J (W.DeltaAll J) K d ε) = 1 ∧
        (∀ r, W.itCount J (W.DeltaAll J) K d ε r ≠ 0 →
          r.2.1 ≤ C * ((W.itInputSize J + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d) ∧
        (3 / 4 : ℝ≥0∞) ≤ probOf (W.itCount J (W.DeltaAll J) K d ε) fun Nh =>
          (1 - ε) * (W.numIT J : ℚ) ≤ Nh ∧ Nh ≤ (1 + ε) * (W.numIT J : ℚ)) ∧
    -- (ii) product weights
    (∀ {n : ℕ} (W : Blocks n) (J : SimpleGraph W.Vtx) [DecidableRel J.Adj],
      1 ≤ J.maxDegree → (∀ i x, 9 * (J.maxDegree : ℚ) * W.π i x ≤ 1) →
      0 < W.probIT J ∧
      mass (W.itSampler J (W.DeltaAll J)) = 1 ∧
      (∀ y, law (W.itSampler J (W.DeltaAll J)) y =
        if W.IsIT J y then ENNReal.ofReal ((W.selWeight y / W.probIT J : ℚ) : ℝ) else 0) ∧
      expTicks (W.itSampler J (W.DeltaAll J)) ≤ ((C * (W.itInputSize J + 1) ^ d : ℕ) : ℝ≥0∞) ∧
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
        mass (W.itFpras J (W.DeltaAll J) K d ε) = 1 ∧
        (∀ r, W.itFpras J (W.DeltaAll J) K d ε r ≠ 0 →
          r.2.1 ≤ C * ((W.itInputSize J + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d) ∧
        (3 / 4 : ℝ≥0∞) ≤ probOf (W.itFpras J (W.DeltaAll J) K d ε) fun Zh =>
          (1 - ε) * W.probIT J ≤ Zh ∧ Zh ≤ (1 + ε) * W.probIT J) ∧
    -- (iii) bipartite hosts
    (∀ {n : ℕ} (W : Blocks n) (J : SimpleGraph W.Vtx) [DecidableRel J.Adj] (side : Fin n → Bool)
      (ΔA ΔB : ℕ),
      1 ≤ J.maxDegree → (∀ u v, J.Adj u v → side u.1 ≠ side v.1) → 1 ≤ ΔA → 1 ≤ ΔB →
      (∀ u, side u.1 = true → J.degree u ≤ ΔA) → (∀ u, side u.1 = false → J.degree u ≤ ΔB) →
      (∀ i x, side i = true → 9 * (ΔB : ℚ) * W.π i x ≤ 1) →
      (∀ i x, side i = false → 9 * (ΔA : ℚ) * W.π i x ≤ 1) →
      0 < W.probIT J ∧
      mass (W.itSampler J (W.DeltaSide J side)) = 1 ∧
      (∀ y, law (W.itSampler J (W.DeltaSide J side)) y =
        if W.IsIT J y then ENNReal.ofReal ((W.selWeight y / W.probIT J : ℚ) : ℝ) else 0) ∧
      expTicks (W.itSampler J (W.DeltaSide J side)) ≤
        ((C * (W.itInputSize J + 1) ^ d : ℕ) : ℝ≥0∞) ∧
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
        mass (W.itFpras J (W.DeltaSide J side) K d ε) = 1 ∧
        (∀ r, W.itFpras J (W.DeltaSide J side) K d ε r ≠ 0 →
          r.2.1 ≤ C * ((W.itInputSize J + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d) ∧
        (3 / 4 : ℝ≥0∞) ≤ probOf (W.itFpras J (W.DeltaSide J side) K d ε) fun Zh =>
          (1 - ε) * W.probIT J ≤ Zh ∧ Zh ≤ (1 + ε) * W.probIT J) := by sorry

end SamplingLLL.Supplement
