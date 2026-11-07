-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_5_3_prime_profiles
-- name    : SubexpPrimes.lemma_5_3_prime_profiles
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:36.0632+00:00
-- url     : https://prove2.me/theorems/f6599003-5644-4bb7-a0ff-670330bb145e
-- title:
--   Lemma 5.3 — the prime profiles: $n$ linear-size networks approximating $W_C$ uniformly in $C$
-- statement:
--   Let $n\ge2$, $Q\ge1$, $P=n+2Q+4$, and let $C$ be admissible. For each $e\in[n]$ there is an explicit network $G_e$ with $O(n+Q)$ edges and degree $O((n+Q)^{3/4})$. It has $O(n+Q)$ weighted vertices, whose entries lie in $[-1,1]$ and have precision $O(n+Q)$, and all its other entries are Boolean. These networks satisfy
--
--   $$
--   \Big|\sum_{e=1}^n\mu(e)\,2^{-P}Z(G_e)-W_C\Big|\le n(n+1)^2\,2^{n-Q}.
--   $$
--
--   The bound holds for every $C$, however few primes satisfy it. This is where the gap of $W_C$ at zero is preserved.
--
--   Differences from the source:
--   - reading: there is a network → an explicit family: one builder machine, one entry machine, one constant, all polynomial; reason: Definition 2.3 and p.28 ("the arithmetic parts are explicit, and the rotation constants take time poly(p)") claim it, and Theorem 2.5 evaluates only such networks; this is the stronger reading and it implies the bare existence
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - encoding: C admissible: constructed, and its entries computed, in time poly(n + L) → builder and entry machine of the admissible family bounded in time and space by one polynomial; reason: in the PrimitiveMachine model the visited space is at most the input length plus the number of tapes times (time + 1), and the inputs here have length polynomial in the same quantity, so a time bound gives the space bound with a larger constant; the constant is universally quantified, so no instance is lost
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 5.3, p.26

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_Admissible
import Definitions.Def_SubexpPrimes_primeMass

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open scoped ArithmeticFunction.Moebius in
/-- **Lemma 5.3 (Prime profiles)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.26.

Let `n ≥ 2`, `Q ≥ 1`, `P = n + 2Q + 4`, and let `C` be admissible. For each `e ∈ [n]` there is an
explicit network `G_e` with `O(n + Q)` edges and degree `O((n + Q)^{3/4})`, with `O(n + Q)` weighted
vertices, whose entries lie in `[-1, 1]` and have precision `O(n + Q)`, and Boolean entries elsewhere,
such that `|∑_{e=1}^n µ(e) 2^{-P} Z(G_e) - W_C| ≤ n(n+1)² 2^{n-Q}`.

**Formalization Note.** The family is indexed by `(n, Q, e, d)`, and `K` is fixed before all of them,
so the error bound is uniform in `C`, however few primes satisfy it. `W_C` is `primeMass`. -/
theorem lemma_5_3_prime_profiles {δ : Type} (encD : δ → List Bool) (C : ℕ → δ → List Bool → Prop)
    (hC : Admissible encD C) :
    ∃ (G : ℕ × ℕ × ℕ × δ → NetDesc) (T : (D : NetDesc) → D.Tables ℚ),
      ExplicitFamily
        (fun a => Encoding.encodeList id [List.replicate a.1 true, List.replicate a.2.1 true,
          List.replicate a.2.2.1 true, encD a.2.2.2])
        (fun a => 2 ≤ a.1 ∧ 1 ≤ a.2.1 ∧ a.2.2.1 ∈ Finset.Icc 1 a.1) G T ∧
      ∃ K : ℕ, ∀ (n Q : ℕ) (d : δ), 2 ≤ n → 1 ≤ Q →
        (∀ e ∈ Finset.Icc 1 n,
          let D := G (n, Q, e, d)
          D.m ≤ K * (n + Q) ∧
          (D.maxDeg : ℝ) ≤ (K : ℝ) * ((n : ℝ) + Q) ^ ((3 : ℝ) / 4) ∧
          D.W.card ≤ K * (n + Q) ∧ D.prec ≤ K * (n + Q) ∧ D.EntriesInRange (T D)) ∧
        |∑ e ∈ Finset.Icc 1 n, ((μ e : ℤ) : ℝ) * (2 : ℝ) ^ (-((n + 2 * Q + 4 : ℕ) : ℤ)) *
              ((((G (n, Q, e, d)).net (T (G (n, Q, e, d)))).Z : ℚ) : ℝ) -
            primeMass n (C n d)| ≤
          (n : ℝ) * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((n : ℤ) - (Q : ℤ)) := by sorry

end SubexpPrimes
