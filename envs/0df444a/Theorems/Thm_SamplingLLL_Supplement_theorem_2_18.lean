-- Prove2me | Theorems.Thm_SamplingLLL_Supplement_theorem_2_18
-- name    : SamplingLLL.Supplement.theorem_2_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:58:07.674811+00:00
-- url     : https://prove2.me/theorems/6e0cbf83-fc3d-4e6b-b595-9d3a0f133d45
-- title:
--   Theorem 2.18, p.10 — random scopes, adversarial signs: counting and sampling random $k$-CNF up to density $c\,2^k/k^2$
-- statement:
--   There are an absolute constant $c>0$, absolute constants $C_0$, $A_{\mathrm{seed}}$ and a threshold $k_0$ such that, for every $k\ge k_0$, the algorithm $A_k$ (with its internal constants fixed, depending on $k$ only) has the following property. Let $0<\alpha\le c\,2^k/k^2$ be fixed and choose $m=\lfloor\alpha n\rfloor$ clause scopes independently and uniformly from the $k$-subsets of $[n]$ (Definition 2.17). With probability tending to one as $n\to\infty$ over the scopes, simultaneously for every assignment of literal signs and every rational $\varepsilon\in(0,1)$:
--
--   1. the formula is satisfiable;
--   2. $A_k$, given the formula and $\varepsilon$, outputs a number within relative error $\varepsilon$ of the number of satisfying assignments with probability at least $3/4$;
--   3. $A_k$ returns a satisfying assignment whose law is within total variation distance $\varepsilon$ of the uniform law on satisfying assignments;
--   4. the expected running time of both is at most
--   $$
--   \Bigl(\frac{n+\ell(\varepsilon)}{\varepsilon}\Bigr)^{C(k)},\qquad C(k)=2^{C_0k}.
--   $$
--
--   This is counting and sampling for random $k$-CNF at clause density of order $2^k/k^2$ when the adversary chooses the signs after seeing the scopes.
--
--   **Formalization Note** $A_k$ is the pair of procedures `akCount`, `akSample`: compute $\alpha=m/n$ and $\Delta=\lceil A_{\mathrm{seed}}(\alpha k+k\log k)\rceil$, perform the peeling and closure of p.57, and run the algorithms of Theorem F.6 with $a_{\mathrm{blk}}=d/8$ and $\beta=4$. Both terminate with probability one, which is part of the statement. The probability over the scopes is `scopeProb`, and "with high probability" is the limit $n\to\infty$.
--
--   Differences from the source:
--   - reading: "for every $k$, a randomized algorithm $A_k$" → $A_k$ is the explicit pair of procedures `akCount`, `akSample` of p.66, with no existential quantifier over programs; reason: the base mission's `Proc` has no machine model, so an existential over programs would make every running-time clause vacuous; this is the convention of the published Theorem 2.6
--   - reading: the algorithm of p.66 uses the constant $A_{\mathrm{seed}}$ ("Choose the seed-threshold constant"), the constant of $T_{\mathrm{core}}=O(\cdot)$ in (67) and "sixteen times the proved polynomial upper bound" (p.57) without giving their values → $A_{\mathrm{seed}}$ is quantified existentially before $k$; $C_{\mathrm{core}}$ and the cap polynomial $(K,e)$ existentially after $k$ and before $\alpha$; reason: these are the constants of the paper's own algorithm; $A_k$ may depend on $k$ only, through the absolute constant $A_{\mathrm{seed}}$ (p.66)
--   - reading: "With high probability over the random clause scopes" → the probability of the event tends to one as $n\to\infty$, the event quantifying over all sign patterns and all $\varepsilon$ inside; reason: the paper's own reading (pp.57, 65: "with probability tending to one")
--   - reading: "The expected running time is $(n/\varepsilon)^{C(k)}$ with $C(k)=2^{O(k)}$" → expected ticks at most $((n+\ell(\varepsilon))/\varepsilon)^{2^{C_0k}}$ with $C_0$ absolute, for $\varepsilon$ rational; reason: the accuracy is a rational given in binary and reading it is charged; the two bounds agree when $\varepsilon$ is written with $O(\log(1/\varepsilon))$ bits
--   - encoding: "$k$ sufficiently large and fixed"; "approximates within relative error $\varepsilon$ with probability at least $3/4$"; "returns a satisfying assignment" → $k\ge k_0$; both procedures terminate with probability one; every output of the sampler satisfies all clauses; reason: the usual meaning of the phrases; termination is needed for the output laws to be probability laws
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Definition 2.17 and Theorem 2.18, p.10; proof on pp.57–66 (F.6–F.9); algorithms of Theorem F.6, pp.55–57

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_peelCore

set_option autoImplicit false

open scoped ENNReal
open Filter Topology

namespace SamplingLLL.Supplement

open Proc

/-- Theorem 2.18 (Random scopes, adversarial signs), p.10. There are an absolute constant `c > 0` and, for
every `k`, a randomized algorithm `A_k` with the following property. Let `k` be sufficiently large and
fixed, let `0 < α ≤ c 2^k/k²` be fixed, and take `m = ⌊αn⌋` clause scopes independently and uniformly from
the `k`-subsets of `[n]` (Definition 2.17). With probability tending to one as `n → ∞` over the scopes,
simultaneously for every assignment of literal signs and every rational `ε ∈ (0,1)`: the formula is
satisfiable; `A_k`, given the formula and `ε`, (i) approximates its number of satisfying assignments within
relative error `ε` with probability at least `3/4`, and (ii) returns a satisfying assignment whose law is
within total variation distance `ε` of the uniform law on satisfying assignments; and the expected running
time of both is at most `((n + ℓ(ε))/ε)^{C(k)}` with `C(k) = 2^{C₀ k}`, `C₀` absolute.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Definition 2.17 and Theorem 2.18,
p.10; proof on pp.65–66 (F.6–F.9), with the algorithms of Theorem F.6, pp.55–57.

**Formalization Note.** `A_k` is the pair of explicit procedures `akCount` and `akSample` of p.66: compute
`α = m/n` and `∆ = ⌈A_seed(αk + k log k)⌉`, perform the peeling and closure of p.57, and run the algorithms
of Theorem F.6 with `a_blk = d/8`, `β = 4`. The seed constant `A_seed` is absolute ("Choose the
seed-threshold constant `A_seed`", p.65) and is quantified before `k`; the constants of Theorem F.6's
algorithms that the paper leaves implicit (`C_core` of (67) and the work-cap polynomial `K ·^e`) are
quantified after `k` and before `α`, so `A_k` depends on `k` only. "With high probability" is the limit
`n → ∞` (pp.57, 65), of an event that quantifies over all signs and all `ε` inside. The accuracy `ε` is a
rational given in binary and reading it is charged, so the time bound is in `(n + bits ε)/ε` (the paper's
`n/ε` when `ε` is written with `O(log(1/ε))` bits). "Sufficiently large `k`" is `k ≥ k₀`. -/
theorem theorem_2_18 : ∃ c : ℝ, 0 < c ∧ ∃ C₀ Aseed k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ Ccore K e : ℕ,
    ∀ α : ℝ, 0 < α → α ≤ c * 2 ^ k / (k : ℝ) ^ 2 →
    Tendsto (fun n : ℕ => scopeProb n ⌊α * (n : ℝ)⌋₊ k fun scope =>
        ∀ (sgn : Fin ⌊α * (n : ℝ)⌋₊ → Fin n → Bool) (ε : ℚ), 0 < ε → ε < 1 →
          let I := kcnf scope sgn
          let T : ℝ := (((n : ℝ) + bits ε) / ε) ^ (2 ^ (C₀ * k))
          (∃ x, I.toCSP.sat Finset.univ x = true) ∧
          mass (akCount k Aseed Ccore K e scope sgn ε) = 1 ∧
          (3 / 4 : ℝ≥0∞) ≤ probOf (akCount k Aseed Ccore K e scope sgn ε) (fun Nh =>
            (1 - ε) * (numSat I : ℚ) ≤ Nh ∧ Nh ≤ (1 + ε) * (numSat I : ℚ)) ∧
          expTicks (akCount k Aseed Ccore K e scope sgn ε) ≤ ENNReal.ofReal T ∧
          mass (akSample k Aseed Ccore scope sgn ε) = 1 ∧
          SupportedOn (akSample k Aseed Ccore scope sgn ε)
            (fun x => I.toCSP.sat Finset.univ x = true) ∧
          tvDist (akSample k Aseed Ccore scope sgn ε)
            (fun x => if I.toCSP.sat Finset.univ x = true then (numSat I : ℝ)⁻¹ else 0) ≤ ε ∧
          expTicks (akSample k Aseed Ccore scope sgn ε) ≤ ENNReal.ofReal T)
      atTop (𝓝 1) := by sorry

end SamplingLLL.Supplement
