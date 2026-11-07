-- Prove2me | Theorems.Thm_SamplingAC0_theorem_4
-- name    : SamplingAC0.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:39.590598+00:00
-- url     : https://prove2.me/theorems/2598f3b5-ffdb-4b6b-b71c-0efe32b7bea5
-- title:
--   Theorem 4 — explicit power-size DNFs sample a distribution far from every depth-$n^c$ forest
-- statement:
--   There are absolute constants $c_1,c_2,c_3>0$ and $N$ such that for every $n\ge N$ (and every encoding of field elements by bits) the distribution $D_n$ on $n$ bits sampled by the $n$ explicit DNFs of the padded sampler (independent copies of the point-line distribution $R$, padded with constant-$0$ outputs) satisfies:
--
--   1. each of the $n$ DNFs has size at most $n^{c_1}$, and
--   2. every forest $f$ with $n$ output bits and depth at most $n^{c_2}$, on any number of input bits, has
--   $$\Delta\bigl(f(U),D_n\bigr)>1-2^{-n^{c_3}} .$$
--
--   Power-size DNFs, a subclass of AC0, sample a distribution that decision forests of polynomial depth cannot even approximate with non-negligible overlap. Earlier separations needed logarithmic depth or distributions not samplable in AC0.
--
--   **Formalization Note** The DNFs are the named definition written out term by term; no claim is made about the cost of producing them. DNF size counts terms and literal occurrences. Forests are adaptive; depth is the worst-case number of queries.
--
--   Differences from the source:
--   - reading: "There is a distribution D on n bits" → for every n ≥ N, D_n = q^13 independent copies of R for the largest q = 2^k with q^13(q² + 2qk) ≤ n, padded with constant-0 bits; reason: the stronger of the two readings (every large n rather than infinitely many n); the padding is this formalization's construction
--   - generalization: explicit DNFs recording points with one unnamed encoding → every encoding enc, with c₁, c₂, c₃, N chosen before enc; reason: the statement for every encoding specializes to the paper's
--   - encoding: "n explicit DNFs of size n^c"; "depth ≤ n^c"; c-notation → the named definition hardSampler written out term by term; size = terms + literal occurrences; a fixed output layout; depth a real bound on worst-case queries; any input length s; three constants before n; reason: same instances; the size measure is at least the term count and forests are closed under permuting outputs
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 4, p.3 (derivation p.8)

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_DNF
import Definitions.Def_SamplingAC0_lineDNF
import Definitions.Def_SamplingAC0_hardSampler
set_option autoImplicit false

namespace SamplingAC0

/-- **Theorem 4 (separating DNF from forest samplers).** Riazanov–Viola, *Sampling Tools and the
Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 4, p.3: "There is a
distribution D on n bits sampled by n explicit DNFs of size n^c such that every forest f of depth
≤ n^c has ∆(f(U), D) > 1 − 2^{−n^c}."

`D` is the law of the explicit DNF sampler `hardSampler enc n` (`t = q^{13}` independent copies of
the point-line distribution `R` of §3, p.8, padded with constant-0 bits up to `n`).

**Formalization Note.** The three occurrences of `c` are three absolute constants, all chosen before
`n` (c-notation, p.2); "on n bits" is claimed for every `n ≥ N`; the statement holds for every
encoding of field elements by bits; DNF size counts terms and literal occurrences; forests are
adaptive, of any input length `s`, with depth = worst-case number of queries. -/
theorem theorem_4 : ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ ∃ N : ℕ,
    ∀ (enc : Encoding) (n : ℕ), N ≤ n →
    (∀ j, ((hardSampler enc n j).size : ℝ) ≤ (n : ℝ) ^ c₁) ∧
    ∀ (s : ℕ) (f : Forest s (Fin n)), f.DepthLE ((n : ℝ) ^ c₂) →
      tvDist (law f.eval) (law (fun x : HardIn n → Bool => fun j => (hardSampler enc n j).eval x))
        > 1 - (2 : ℝ) ^ (-((n : ℝ) ^ c₃)) := by sorry

end SamplingAC0
