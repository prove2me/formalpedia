-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_5_1_cosine_chain
-- name    : SubexpPrimes.lemma_5_1_cosine_chain
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:59.555746+00:00
-- url     : https://prove2.me/theorems/1439120e-b582-4e3e-97b4-d466f003712a
-- title:
--   Lemma 5.1 — the cosine chain: a network whose contraction approximates $\mu(d)$
-- statement:
--   Let $H,Q\ge1$, and put $q=H+Q+8$ and $p=H+Q+\lceil\log q\rceil+8$. There is an explicit network with an $H$-bit input $d$, $O(H+Q)$ edges and degree $O((H+Q)^{3/4})$, with the following properties. All of its non-Boolean entries lie at $q$ vertices, and they belong to $2^{-p}\mathbb Z\cap[-1,1]$. For $1\le d<2^H$, its contraction $\nu(d)$ with the input fixed to $d$ satisfies
--
--   $$
--   |\nu(d)-\mu(d)|\le2^{-Q}.
--   $$
--
--   It is the only part of the construction with non-Boolean entries, and it is why the contraction lemma is needed with real weights.
--
--   **Formalization Note** The explicit clause is essential here: with bare existence, the entries could hold constants that no algorithm computes.
--
--   Differences from the source:
--   - reading: there is a network → an explicit family: one builder machine, one entry machine, one constant, all polynomial; reason: Definition 2.3 and p.28 ("the arithmetic parts are explicit, and the rotation constants take time poly(p)") claim it, and Theorem 2.5 evaluates only such networks; this is the stronger reading and it implies the bare existence
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 5.1, p.22

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_ExplicitFamily
import Definitions.Def_SubexpPrimes_bitsToNat

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open scoped ArithmeticFunction.Moebius in
/-- **Lemma 5.1 (Cosine chain)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.22.

Let `H, Q ≥ 1`, `q = H + Q + 8` and `p = H + Q + ⌈log q⌉ + 8`. There is an explicit network with an
`H`-bit input `d`, `O(H + Q)` edges and degree `O((H + Q)^{3/4})`, whose non-Boolean entries lie at
`q` vertices and belong to `2^{-p}ℤ ∩ [-1, 1]`, such that for `1 ≤ d < 2^H`, its contraction `ν(d)`
with the input fixed to `d` satisfies `|ν(d) - µ(d)| ≤ 2^{-Q}`.

**Formalization Note.** The family is indexed by `(H, Q)`, and the explicit clause is essential: with
a bare existence the entries could hold constants no algorithm computes, and Theorem 2.5 could not
evaluate the network. `⌈log q⌉` is `Nat.clog 2 q`. -/
theorem lemma_5_1_cosine_chain :
    ∃ (G : ℕ × ℕ → NetDesc) (T : (D : NetDesc) → D.Tables ℚ),
      ExplicitFamily
        (fun a => Encoding.encodeList id [List.replicate a.1 true, List.replicate a.2 true])
        (fun a => 1 ≤ a.1 ∧ 1 ≤ a.2) G T ∧
      ∃ K : ℕ, ∀ H Q : ℕ, 1 ≤ H → 1 ≤ Q →
        let D := G (H, Q)
        let q := H + Q + 8
        let p := H + Q + Nat.clog 2 q + 8
        D.inputs.length = H ∧ D.inputs.Nodup ∧
        D.m ≤ K * (H + Q) ∧
        (D.maxDeg : ℝ) ≤ (K : ℝ) * ((H : ℝ) + Q) ^ ((3 : ℝ) / 4) ∧
        D.W.card = q ∧ D.prec = p ∧ D.EntriesInRange (T D) ∧
        ∀ d : List Bool, d.length = H → 1 ≤ bitsToNat d →
          |(((D.net (T D)).ZFixed D.inputs d : ℚ) : ℝ) - ((μ (bitsToNat d) : ℤ) : ℝ)| ≤
            (2 : ℝ) ^ (-(Q : ℤ)) := by sorry

end SubexpPrimes
