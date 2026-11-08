-- Prove2me | Theorems.Thm_SpikyCVP_theorem_2_10
-- name    : SpikyCVP.theorem_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:52:51.416781+00:00
-- url     : https://prove2.me/theorems/d76e2ba1-b2b3-4e48-b2d0-40c74558bbde
-- title:
--   Theorem 2.10 ([ADS15], Corollary 6.5) — Euclidean CVP in $2^{n+o(n)}\mathrm{poly}(|I|)$ time
-- statement:
--   There are a machine, a constant $K$ and a function $f$ with $f(n)/n\to0$ such that for every $n$, every basis $B\in\mathbb Q^{n\times n}$ of a lattice $\mathcal L$ of rank $n$ and every target $t\in\mathbb Q^n$, with $\ell$ the length of the encoding of $(n,B,t)$ and
--
--   $$T=\big\lceil 2^{n+f(n)}(\ell+1)^K\big\rceil,$$
--
--   the machine, on the instance followed by any string of $T$ coins, halts within $2T$ steps with a vector of $\mathcal L$, and for at least half of the coin strings this vector is a closest vector to $t$ in the $\ell_2$ norm.
--
--   This is the result of Aggarwal, Dadush and Stephens-Davidowitz (FOCS 2015) that the paper uses as its Euclidean subroutine; it is applied in a diagonal metric to a coset of $2\mathcal L$. The deterministic $2^{2n+o(n)}$ algorithm of Micciancio and Voulgaris may replace it.
--
--   Differences from the source:
--   - reading: a randomized algorithm, analyzed in the real-RAM model of §2.1 → one Mathlib TM2 machine, run per input (Turing.TM2OutputsInTime), with coins as a suffix of the input of length exactly T; reason: [ADS15] is a rational-input algorithm and p.10 asserts the word-RAM transfer; a TM2 has to pop unused coins, hence 2T
--   - reading: it runs in time 2^{n+o(n)}poly(|I|) → halts within 2T steps on every coin string, T = ⌈2^{n+f(n)}(ℓ+1)^K⌉₊ with f(n)/n → 0 and K, f chosen before the instance; reason: [ADS15] states its bound as a running time; the polynomial in |I| is a polynomial in the input length ℓ
--   - encoding: with probability at least 1/2, a closest vector to t in the ℓ2 norm → the fraction of coin strings whose output encVec x satisfies IsClosest 2 B t x is at least 1/2; closeness compared through Σ_j |x_j − t_j|²; reason: T fair coins; comparing squares is equivalent to comparing ℓ2 norms
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Theorem 2.10, p.15 (PDF p.17), citing [ADS15] Corollary 6.5

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_SpikyCVP_latt
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_SpikyCVP_RunsWithin

open Filter Topology PNormReg

namespace SpikyCVP

/-- **Theorem 2.10 ([ADS15], Corollary 6.5): Euclidean CVP in `2^{n+o(n)}poly(|I|)` time.**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Theorem 2.10, p.15 (PDF p.17), citing Aggarwal, Dadush, Stephens-Davidowitz, FOCS 2015, Corollary 6.5.

There are a machine, a constant `K` and a function `f(n) = o(n)` such that for every `n`, every basis
`B ∈ Q^{n×n}` of a lattice `L` of rank `n` and every target `t ∈ Qⁿ`, with `ℓ` the input length and
`T = ⌈2^{n+f(n)}(ℓ+1)^K⌉`: on the input followed by any `T` coins the machine halts within `2T` steps with a
vector of `L`, and for at least half of the coin strings that vector is a closest vector to `t` in `ℓ2`.

**Formalization Note.** Mathlib's TM2, run per input; coins are a suffix of length exactly `T`; `2T` because
a halting TM2 must pop the coins it did not use. -/
theorem theorem_2_10 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (K : ℕ) (f : ℕ → ℝ),
      Tendsto (fun n : ℕ => f n / n) atTop (𝓝 0) ∧
      ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℚ) (t : Fin n → ℚ), B.det ≠ 0 →
        let T := budgetADS f K n (encCVP B t).length
        (∀ coins : List.Vector Bool T, ∃ x : Fin n → ℚ,
          (fun j => (x j : ℝ)) ∈ latt (B.map fun q : ℚ => (q : ℝ)) ∧
          RunsWithin M (encCVP B t ++ coins.toList) (encVec x) (2 * T)) ∧
        1 / 2 ≤ coinFraction T fun coins =>
          ∃ x : Fin n → ℚ, IsClosest 2 B t x ∧ RunsWithin M (encCVP B t ++ coins) (encVec x) (2 * T) := by sorry

end SpikyCVP
