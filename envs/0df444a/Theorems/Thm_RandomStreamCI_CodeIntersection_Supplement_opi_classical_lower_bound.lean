-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_Supplement_opi_classical_lower_bound
-- name    : RandomStreamCI.CodeIntersection.Supplement.opi_classical_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:52:21.91995+00:00
-- url     : https://prove2.me/theorems/bff07a15-26c5-4d04-a8fe-13d293c30d2d
-- title:
--   Theorem 27 (companion theorem; not used in the proof of the goal) — Optimal Polynomial Intersection lower bound
-- statement:
--   For Problem 2 let $d(n)$ be any admissible degree family with $d(n)=\omega(\log_2 n)$ and $d(n)=o(n/\log_2 n)$. Put
--   $$\tau(n)=\left\lceil n/2+\sqrt{d(n)n}/8\right\rceil.$$
--   There exist constants $c,a>0$ and a threshold $N$ such that, at every admissible $n\ge N$, for every characteristic-two field of size $q=n+1$, every enumeration of its nonzero evaluation points, and every randomized one-pass classical program using $S\le cn$ bits,
--   $$\Pr_{H,\pi,\mathrm{coins}}[\text{output has score at least }\tau(n)]\le 2^{-a d(n)}.$$
--   The output must be in the Reed–Solomon code, equivalently a polynomial of degree strictly below $d(n)$; abort and invalid outputs fail. Oracle and order are independent and uniform, and the coins are independent of both. The constants and threshold precede all algorithms. This is a companion theorem, not a prerequisite for the published Code Intersection goal.
--
--   Differences from the source:
--   - encoding: coordinates, times and symbols as finite labelled sets → Fin indices numbered from zero and finite alphabet types; reason: bijections of labels preserve every source instance
--   - encoding: q any power of two, n=q-1 and distinct nonzero evaluation points → every finite field of characteristic two with cardinality n+1 and every nonzero embedding Fin n into it; reason: all finite fields and evaluation enumerations in Problem 2 are covered, including non-prime fields
--   - encoding: asymptotics along source-admissible n and unspecified eventual constants → the filter atTop restricted to all n+1=2^e, and explicit positive constants and thresholds; reason: expands the asymptotic quantifiers without selecting a smaller subsequence
--   - encoding: randomized bounded-memory classical algorithms → width 2^S deterministic transducers mixed with independent finite PMF coins; reason: on finite input and state spaces any random tape induces a finite distribution on deterministic behaviors, with identical success
--   - encoding: degree-strictly-below-d polynomials and their evaluation code → published coefficient-polynomial and general GRS evaluation definitions, with unit multipliers; reason: degree < d has exactly d coefficients, and distinct evaluation on n>=d points is injective, so codeword and polynomial outputs are isomorphic
--   - encoding: d=omega(log n) and d=o(n/log n) → log_2(n)/d(n) tends to zero and d(n)*log_2(n)/n tends to zero on admissible lengths; reason: the ratios are equivalent in the eventual positive-log regime n>=3
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Theorem 27, p. 22 (printed = PDF; offset 0)

import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Asymptotics

namespace RandomStreamCI.CodeIntersection.Supplement

open Filter Topology

/-- Theorem 27, pp. 22--23: full linear-memory lower bound, including independent coins.
Constants and threshold follow the degree family and precede all fields and algorithms. -/
theorem opi_classical_lower_bound (d : ℕ → ℕ) (hd : DegreeFamily d)
    (hlarge : Tendsto (fun n : ℕ => log₂ (n : ℝ) / (d n : ℝ)) opiAtTop (𝓝 0))
    (hsmall : Tendsto (fun n : ℕ => (d n : ℝ) * log₂ (n : ℝ) / (n : ℝ))
      opiAtTop (𝓝 0)) :
    ∃ c a : ℝ, 0 < c ∧ 0 < a ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ hn : AdmissibleLength n,
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = n + 1 → ∀ α : Fin n ↪ F, (∀ i, α i ≠ 0) →
      ∀ S : ℕ, (S : ℝ) ≤ c * n →
      ∀ (Ω : Type) [Fintype Ω] (p : PMF Ω) (B : Ω → BranchingProgram n F (2^S)),
        randomizedTauSuccess p B (rsCode α (d n) (hd n hn).2)
          (target n (d n)) ≤ (2 : ℝ) ^ (-a * (d n : ℝ)) := by sorry

end RandomStreamCI.CodeIntersection.Supplement
