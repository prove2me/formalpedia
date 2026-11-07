-- Prove2me | Theorems.Thm_PDSEquiv_lemma_5_5
-- name    : PDSEquiv.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:44.992557+00:00
-- url     : https://prove2.me/theorems/6f63093d-0c5b-45bf-93fa-2edc15bb1472
-- title:
--   Lemma 5.5 — the nonnegative statistic $w=|T_{n,N}f^{>D}|/R$, its bounds (i), (ii) and its estimator (iii)
-- statement:
--   Fix a rational $q\in(0,1)$ and an integer $D\ge2$. For all sufficiently large $N$, depending only on $q,D$, let $1\le n\le N$ be an integer. Let $O$ be a randomized $\{-1,1\}$-valued distinguisher on $[N]$ and $f(G)=\mathbb E_O[O(G)]\in[-1,1]$. Then $w=|T_{n,N}f^{>D}|/R$, with $R=c_q^{D^2}N^{D+1}$ from (5), is permutation-invariant with values in $[0,1]$ and satisfies, for every $q<p\le1$ and $0\le k\le n$:
--
--   1. $\mathbb E_{G\sim\mathrm{PDS}(n,k,p,q)}[w(G)]\ge\frac1R\bigl|\mathbb E_{Y\sim\mathrm{PDS}(N,k,p,q)}[f^{>D}(Y)]\bigr|$;
--   2. $\mathbb E_{G\sim\mathrm{ER}(n,q)}[w(G)]\le(n/N)^{(D+1)/2}/R$;
--   3. there is a randomized oracle algorithm $B$, depending only on $q,D$, that given $N$, a graph $G$ on $[n]$ and $\zeta\in(0,1)$ outputs $B^O(G,\zeta)\in[0,1]$ with
--   $$\mathbb E_{B,O}\bigl|B^O(G,\zeta)-w(G)\bigr|\le\zeta,$$
--   making $O(\zeta^{-2})$ queries to $O$, all on $N$-vertex graphs, in running time $2^{O(D^2)}N^{O(D)}\zeta^{-2}$, with implicit constants depending only on $q$.
--
--   The statistic $w$ separates planted from null inputs on the small graph, and it can be estimated from black-box access to $O$.
--
--   **Formalization Note** $\zeta=a/b$ is given as two naturals $0<a<b$; the output is a pair $[u,v]$ read as $u/v\in[0,1]$.
--
--   Differences from the source:
--   - reading: running time 2^{O(D²)} N^{O(D)} ζ^{−2} (elementary operations) → ∃ C depending only on q (before D): executed instructions ≤ 2^{C·D²}(N+2)^{C·D}ζ^{−2} on every branch; and in addition log-cost ≤ ((N+2)(⌊b/a⌋+1)(bits a + bits b + 1))^e with e depending on q, D; reason: the printed count is of elementary operations; log-cost (the sense of polynomial time everywhere else) adds bit-length factors unrelated to the page, so both are stated; the proof's algorithm meets both
--   - encoding: O(ζ^{−2}) queries, implicit constants depending only on q → queries ≤ C·ζ^{−2} with the same C; reason: the meaning of O(·) with a constant depending on q only
--   - encoding: N + 2 in place of N in the step bound → (N + 2)^{C·D}; reason: keeps the bound meaningful at every N; for N ≥ N₀ ≥ 2 it differs from N^{O(D)} by a constant factor absorbed by C
--   - encoding: a randomized oracle (distinguisher or search algorithm) on graphs → a family of laws over graphs of every size (DistFamily/SearchFamily), answering a query enc G with [1]/[0] or with the characteristic list of a set, and [] on malformed queries; the hypotheses read it at the stated size only; reason: the black-box oracle of §4.1 with fresh randomness per call; non-uniform oracles are allowed as on the page
--   - reading: randomized polynomial-time algorithm (no machine model named; unit cost for Ber(θ) with O(log N)-bit rational θ, §4.1) → a program of the log-cost RAM PDSEquiv.Machine with exact Ber(a/b) draws for any naturals a ≤ b, charged by bit lengths, halting within (N+2)^c log-cost on every random branch, for every N and every graph; reason: the paper fixes no machine; log-cost RAM time is polynomial Turing-machine time, and allowing every rational θ enlarges both sides of each claim alike while every algorithm of the paper still applies
--   - encoding: inputs N, a graph G on [n] and ζ ∈ (0, 1); output B^O(G, ζ) ∈ [0, 1] → input cells N :: a :: b :: enc G with naturals 0 < a < b and ζ = a/b; output [u, v] with 0 < v and u ≤ v, read as u/v; reason: a machine input or output is a finite list of naturals, so ζ is given exactly as a rational; a real ζ ∈ (0, 1) can be replaced by a rational in [ζ/2, ζ], which only tightens the accuracy
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 5.5, pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Fourier
import Definitions.Def_PDSEquiv_Embed

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 5.5, pp.16–17 (PDF pp.18–19).
The statistic `w = |T_{n,N} f^{>D}| / R` of a distinguisher, its bounds (i), (ii), and the estimator (iii).

**Formalization Note.** `O` is a family of laws `d`, read at size `N`. The estimator's input cells are
`N`, `a`, `b`, then `enc H`, with `ζ = a/b ∈ (0, 1)`; its output is `[u, v]`, read as `u/v ∈ [0, 1]`.
The printed time `2^{O(D²)} N^{O(D)} ζ^{−2}` counts instructions (`steps`), with `C` depending only on
`q`, as printed, and is bounded in `N + 2` so that it needs no lower bound on `N`. The log-cost is
also polynomial in `N`, `1/ζ` and the bits of `a`, `b` (exponent `e`, depending on `q`, `D`): this
is the sense of "polynomial time" in every other statement, and it does not follow from the
instruction count. `N₀`, `P` and `e` depend only on `q`, `D`. -/
theorem lemma_5_5 (q : ℚ) (hq : 0 < q) (hq1 : q < 1) :
    ∃ C : ℕ, ∀ D : ℕ, 2 ≤ D → ∃ (P : Program) (N₀ e : ℕ), ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, 1 ≤ n → n ≤ N →
      ∀ d : DistFamily,
        let f : Graph N → ℝ := signedMean (fun G => distAcc d G)
        let R : ℝ := bigR q D N
        let w : Graph n → ℝ := fun H => |embedT (q : ℝ) (highPart (q : ℝ) D f) H| / R
        PermInvariant w ∧ (∀ H, 0 ≤ w H ∧ w H ≤ 1) ∧
        (∀ p : ℝ, (q : ℝ) < p → p ≤ 1 → ∀ k : ℕ, k ≤ n →
          expect (pdsMass n k p q) w ≥ 1 / R * |expect (pdsMass N k p q) (highPart (q : ℝ) D f)|) ∧
        expect (erMass n q) w ≤ ((n : ℝ) / N) ^ (((D : ℝ) + 1) / 2) / R ∧
        ∀ (a b : ℕ) (H : Graph n), 0 < a → a < b →
          let input : List ℕ := N :: a :: b :: enc H
          let ζ : ℝ := (a : ℝ) / b
          HaltsWithin P (distOracle d) input
              (((N + 2) * (b / a + 1) * (bits a + bits b + 1)) ^ e)
              (((N + 2) * (b / a + 1) * (bits a + bits b + 1)) ^ e) ∧
            StepsQueriesWithin P (distOracle d) input
              ((2 : ℝ) ^ (C * D ^ 2) * ((N : ℝ) + 2) ^ (C * D) * (ζ ^ 2)⁻¹) (C * (ζ ^ 2)⁻¹) ∧
            QueriesSatisfy P (distOracle d) input (IsGraphQuery N) ∧
            OutputsSatisfy P (distOracle d) input IsRatOut ∧
            outExpect P (distOracle d) input (fun o => |ratOut o - w H|) ≤ ζ := by sorry

end PDSEquiv
