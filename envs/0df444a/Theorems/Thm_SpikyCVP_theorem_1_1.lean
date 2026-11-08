-- Prove2me | Theorems.Thm_SpikyCVP_theorem_1_1
-- name    : SpikyCVP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:55:24.528164+00:00
-- url     : https://prove2.me/theorems/44a2447a-1864-4f2b-b47d-43c15d2f5ff7
-- title:
--   Theorem 1.1 — exact $\mathrm{CVP}_p$ for rational $1<p<2$ in $2^{O_p(n)}\mathrm{poly}(|I|)\log(1/\delta)$ time (corrected: $p$ rational)
-- statement:
--   Fix a rational $p\in(1,2)$. There are a machine and constants $C,K$ such that for every $n$, every basis $B\in\mathbb Q^{n\times n}$ of a lattice $\mathcal L\subseteq\mathbb Q^n$ of rank $n$, every target $t\in\mathbb Q^n$ and every rational $\delta\in(0,1/2]$, with $\ell$ the length of the encoding of $(n,B,t,\delta)$ and
--
--   $$T=\Big\lceil 2^{Cn}(\ell+1)^K\log_2(1/\delta)\Big\rceil,$$
--
--   the machine, on the instance followed by any string of $T$ coins, halts within $2T$ steps, and for a fraction at least $1-\delta$ of the coin strings it outputs a vector $x\in\mathcal L$ with
--
--   $$\|x-t\|_p=\min_{y\in\mathcal L}\|y-t\|_p .$$
--
--   This is the main theorem of the paper: the first single-exponential algorithm for exact CVP in a non-Euclidean $\ell_p$ norm without a promise on the target. Previously the best algorithms for exact $\mathrm{CVP}_p$, $p\ne2$, ran in time $n^{O(n)}$ or $(\log 2n)^{O(n)}$.
--
--   Differences from the source:
--   - correction: Fix p ∈ (1, 2) → p rational, 1 < p < 2, fixed before the machine and the constants; reason: on a Turing model the printed statement fails for non-computable p: with w = (−2,…,−2,1,…,1) ∈ Z^{k+m} (k entries −2), H > 4(4k+m+2), L = Zw + HZ^{k+m} and t = (2,…,2,0,…,0) (k twos), the unique closest vector is 0 when k·2^p < m and −w when k·2^p > m, so a machine succeeding with probability ≥ 3/4 decides the cut of 2^p and p would be computable; the paper restricts its word-RAM claim to 'every fixed, rational p' (p.10)
--   - reading: a randomized algorithm, analyzed in the real-RAM model (§2.1) → one Mathlib TM2 machine, run per input (Turing.TM2OutputsInTime), with fair coins given as a suffix of the input of length exactly T; reason: p.10 states the results hold in the word-RAM model with poly(|I|) overhead for rational p; 2^{O(n)}·poly(|I|) is closed under polynomial overhead; a TM2 has to pop unused coins, hence 2T
--   - reading: |I|, the bit length of the input → ℓ, the length of the encoding of (n, B, t, δ), δ included; reason: the machine must read δ, whose code can be much longer than log(1/δ)
--   - generalization: expected time 2^{O_p(n)}·poly(|I|)·log(1/δ) → at most 2T steps on every coin string, T = ⌈2^{Cn}(ℓ+1)^K log₂(1/δ)⌉₊; reason: a worst-case bound implies the expected-time bound for the same machine; the paper's proof gives it after truncating each run at a constant multiple of its expected time (Markov)
--   - encoding: probability at least 1 − δ; a vector of L closest to t in the ℓp norm → the fraction of coin strings with output encVec x, IsClosest p B t x, is at least 1 − δ; closeness compared through ∥·∥p^p in ℝ; reason: T fair coins; comparing p-th powers is equivalent to comparing norms
--   - encoding: δ ∈ (0, 1/2] → δ : ℚ with 0 < δ ≤ 1/2; reason: δ is part of the input of a Turing machine, which is a finite string; for a real δ ∈ (0, 1/2] any rational δ' ∈ [δ/2, δ] gives the printed guarantee with log₂(1/δ') ≤ log₂(1/δ) + 1
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Theorem 1.1, p.3 (PDF p.5); Theorem 4.1 and the amplification sentence, p.18 (PDF p.20); §2.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_SpikyCVP_latt
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_SpikyCVP_RunsWithin

open PNormReg

namespace SpikyCVP

/-- **Theorem 1.1 (Exact CVPp).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Theorem 1.1, p.3 (PDF p.5); proved through Theorem 4.1, p.18 (PDF p.20).

Fix a rational `p ∈ (1, 2)`. There are a machine and constants `C`, `K` such that for every `n`, every basis
`B ∈ Q^{n×n}` of a lattice `L ⊆ Qⁿ` of rank `n`, every target `t ∈ Qⁿ` and every rational `δ ∈ (0, 1/2]`, with `ℓ`
the length of the input `(n, B, t, δ)` and `T = ⌈2^{C·n}(ℓ+1)^K log₂(1/δ)⌉`: on the input followed by any `T`
coins the machine halts within `2T` steps, and for at least a fraction `1 − δ` of the coin strings it outputs
a vector of `L` closest to `t` in the `ℓp` norm.

**Formalization Note.** The paper analyzes a real-RAM and notes the word-RAM transfer "for every fixed,
rational p" (p.10); here the machine is Mathlib's TM2, run per input, and `p` is rational and fixed before
the machine and the constants. The time bound holds on every coin string, which implies the printed
expected-time bound. Coins are a suffix of length exactly `T`; the bound is `2T` because a halting TM2 must
pop the coins it did not use. `ℓ` includes the code of `δ`. Closeness is compared through `∥·∥p^p`, and the
output must lie in `L`. -/
theorem theorem_1_1 (p : ℚ) (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C K : ℕ),
      ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℚ) (t : Fin n → ℚ) (δ : ℚ),
        B.det ≠ 0 → 0 < δ → δ ≤ 1 / 2 →
        let T := budget C K n (encInst B t δ).length δ
        (∀ coins : List.Vector Bool T, ∃ out, RunsWithin M (encInst B t δ ++ coins.toList) out (2 * T)) ∧
        1 - (δ : ℝ) ≤ coinFraction T fun coins =>
          ∃ x : Fin n → ℚ, IsClosest p B t x ∧
            RunsWithin M (encInst B t δ ++ coins) (encVec x) (2 * T) := by sorry

end SpikyCVP
