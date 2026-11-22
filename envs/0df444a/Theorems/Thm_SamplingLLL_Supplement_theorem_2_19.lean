-- Prove2me | Theorems.Thm_SamplingLLL_Supplement_theorem_2_19
-- name    : SamplingLLL.Supplement.theorem_2_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:58:50.398471+00:00
-- url     : https://prove2.me/theorems/31cc7dab-01b3-44ab-82b8-f379bfb9ba78
-- title:
--   Theorem 2.19, p.10 — variable-regular random $k$-CNF: deterministic counting and sampling for $r\le c\,2^k/k$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds for every sufficiently large fixed $k$ and every fixed $1\le r\le c\,2^k/k$. For $n$ with $k\mid rn$, choose a uniformly random simple $(r,k)$-biregular factor graph with $n$ variables of degree $r$ and $m=rn/k$ clauses of size $k$, and then assign the literal signs arbitrarily. With probability tending to one as $n\to\infty$ over the factor graph, simultaneously for every assignment of signs and every rational $\varepsilon\in(0,1)$:
--
--   1. the formula is satisfiable;
--   2. the deterministic counter outputs a number within relative error $\varepsilon$ of the number of satisfying assignments, in time at most $T$;
--   3. the randomized sampler terminates almost surely and returns a satisfying assignment whose law is within total variation distance $\varepsilon$ of the uniform law on satisfying assignments, in expected time at most $T$;
--
--   where
--   $$
--   T=\Bigl(\frac{n+\ell(\varepsilon)}{\varepsilon}\Bigr)^{2^{C_0k}}
--   $$
--   with $C_0$ absolute. At the largest allowed $r$ the clause density $r/k$ is of order $2^k/k^2$.
--
--   **Formalization Note** The algorithms are `cnfCount` and `cnfSample` (pp.48–49): Theorem 5.4's counter and restarted sampler at $p_0=2^{-k+3}$ and the cutoff $L=\max\{2,\lceil\log_2(64mp_0/\min\{\varepsilon,1/2\})\rceil\}$, or exhaustive enumeration when $L>\delta n$. The counter draws no random bits, and its error and time bounds hold for every outcome. The probability over the factor graph is `brProb`, and the limit is along the $n$ with $k\mid rn$.
--
--   Differences from the source:
--   - reading: "a deterministic algorithm approximates … and a randomized algorithm returns …" → the clauses are stated for the explicit procedures `cnfCount` (which draws no random bits) and `cnfSample` of the proof, with no existential quantifier over programs; reason: the base mission's `Proc` has no machine model, so an existential over programs would make every running-time clause vacuous; this is the convention of the published Theorem 2.6
--   - reading: the algorithm of p.49 tests $L\le\delta n$ with $\delta=\delta(k)$ of Lemma F.1, whose value is not given → $\delta$ is a parameter of the procedures, quantified existentially after $k$ and before $r$; reason: it is a constant of the paper's own algorithm, which may depend on the fixed $k$ ("a single $\delta=\delta(k)$", p.48)
--   - reading: "With high probability over the factor graph" → the probability tends to one as $n\to\infty$ along $k\mid rn$, the event quantifying over all sign patterns and all $\varepsilon$ inside; reason: the paper's own reading (Lemma F.1's proof; pp.57, 65)
--   - reading: "in (expected) time $(n/\varepsilon)^{2^{O(k)}}$" → worst-case ticks of the counter and expected ticks of the sampler at most $((n+\ell(\varepsilon))/\varepsilon)^{2^{C_0k}}$ with $C_0$ absolute, for $\varepsilon$ rational; reason: the accuracy is a rational given in binary and reading it is charged; the two bounds agree when $\varepsilon$ is written with $O(\log(1/\varepsilon))$ bits
--   - encoding: "sufficiently large fixed $k$"; "At the largest allowed $r$, the clause density $r/k$ is of order $2^k/k^2$" → $k\ge k_0$; the density remark is not a separate clause; reason: the remark is arithmetic on the hypothesis $r\le c2^k/k$ and asserts nothing about the algorithms
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.19, p.10; Lemma F.1 and proof of Theorem 2.19, pp.48–49

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_cnfData

set_option autoImplicit false

open scoped ENNReal
open Filter Topology

namespace SamplingLLL.Supplement

open Proc

/-- Theorem 2.19 (Variable-regular random k-CNF), p.10. There is an absolute constant `c > 0` such that for
every sufficiently large fixed `k` and every fixed `1 ≤ r ≤ c 2^k/k` the following holds. For `n` with
`k ∣ rn`, choose a uniformly random simple `(r, k)`-biregular factor graph with `n` variables of degree `r` and
`m = rn/k` clauses of size `k`, and assign the literal signs arbitrarily. With probability tending to one as
`n → ∞` over the factor graph, simultaneously for every assignment of signs and every rational
`ε ∈ (0,1)`: the formula is satisfiable; the deterministic counter approximates its number of satisfying
assignments within relative error `ε` in time `((n + ℓ(ε))/ε)^{2^{C₀ k}}`; and the randomized sampler
terminates almost surely and returns a satisfying assignment whose law is within total variation distance
`ε` of the uniform law on satisfying assignments, in expected time `((n + ℓ(ε))/ε)^{2^{C₀ k}}`. Here `C₀` is
absolute and `ℓ(ε) = bits ε` is the bit length of the rational `ε`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.19, p.10; proof on
pp.48–49 (Lemma F.1 and Theorem 5.4).

**Formalization Note.** The algorithms are the explicit procedures `cnfCount` and `cnfSample` of the proof
(Theorem 5.4's counter and restarted sampler at `p₀ = 2^{−k+3}` and the cutoff `L` of p.48, or exhaustive
enumeration when `L > δn`). The expansion constant `δ = δ(k)` of Lemma F.1 is not explicit in the paper; it is
a parameter of the procedures, quantified existentially after `k`, as the paper's algorithm may depend on
the fixed `k`. "With high probability" is the limit along `n` with `k ∣ rn`; "`2^{O(k)}`" is `2^{C₀ k}` with
`C₀` absolute, chosen before `k`. The accuracy `ε` is a rational given in binary and reading it is charged,
so the time bound is in `(n + bits ε)/ε` (the paper's `n/ε` when `ε` is written with `O(log(1/ε))` bits, the
base mission's convention for Theorem 2.6). The counter draws no random bits and its bounds hold for every outcome.
"At the largest allowed `r`, the clause density `r/k` is of order `2^k/k²`" is arithmetic on `r ≤ c 2^k/k`
and is not a separate clause. -/
theorem theorem_2_19 : ∃ c : ℝ, 0 < c ∧ ∃ C₀ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ δ : ℚ, 0 < δ ∧
    ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ c * 2 ^ k / k →
    Tendsto (fun n => brProb n k r fun scope =>
        ∀ (sgn : Fin (r * n / k) → Fin n → Bool) (ε : ℚ), 0 < ε → ε < 1 →
          let I := kcnf scope sgn
          let T : ℝ := (((n : ℝ) + bits ε) / ε) ^ (2 ^ (C₀ * k))
          (∃ x, I.toCSP.sat Finset.univ x = true) ∧
          mass (cnfCount k δ I ε) = 1 ∧
          (∀ q, cnfCount k δ I ε q ≠ 0 →
            (1 - ε) * (numSat I : ℚ) ≤ q.1 ∧ q.1 ≤ (1 + ε) * (numSat I : ℚ) ∧ (q.2.1 : ℝ) ≤ T) ∧
          mass (cnfSample k δ I ε) = 1 ∧
          SupportedOn (cnfSample k δ I ε) (fun x => I.toCSP.sat Finset.univ x = true) ∧
          tvDist (cnfSample k δ I ε)
              (fun x => if I.toCSP.sat Finset.univ x = true then (numSat I : ℝ)⁻¹ else 0) ≤ ε ∧
          expTicks (cnfSample k δ I ε) ≤ ENNReal.ofReal T)
      (atTop ⊓ 𝓟 {n | k ∣ r * n}) (𝓝 1) := by sorry

end SamplingLLL.Supplement
