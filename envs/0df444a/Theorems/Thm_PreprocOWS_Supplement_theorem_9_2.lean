-- Prove2me | Theorems.Thm_PreprocOWS_Supplement_theorem_9_2
-- name    : PreprocOWS.Supplement.theorem_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:13:27.94014+00:00
-- url     : https://prove2.me/theorems/c029ede0-55da-4c76-8d31-a6f64c08be44
-- title:
--   Theorem 9.2 — one-query search for binary phase states: $\mathbb E_R[\mathrm{Win}(\mathcal A\mid R)]\le 2(1+\log(2M))/K$
-- statement:
--   Let $R=(R(k,x))_{k\in[K],x\in[N]}$ be independent Rademacher signs and $|\psi_{R,k}\rangle = N^{-1/2}\sum_x R(k,x)|x\rangle$. A one-query adversary with workspace dimension $M$ consists of an isometry $V:\mathbb C^N\to\mathbb C^M$ and a projective measurement $\{\Pi_k\}_{k\in[K]}$ on $\mathbb C^M$, both independent of $R$, and a phase function $f_R:[M]\to\{\pm1\}$ that may depend arbitrarily on $R$ but not on $k$.
--
--   For all $K\ge1$, $N$, $M$ and every such adversary,
--   $$
--   \mathbb E_R\Big[\max_f\ \mathbb E_k\big\|\Pi_k\,O_f\,V|\psi_{R,k}\rangle\big\|^2\Big]\,\le\,\frac{2\,(1+\log(2M))}{K},
--   $$
--   where $\log$ is the natural logarithm.
--
--   The bound says that one query to an arbitrary phase oracle barely helps to identify a random binary phase state, which yields one-query unitary synthesis lower bounds.
--
--   Differences from the source:
--   - reading: log (base not stated) → natural logarithm Real.log; reason: ln(2M) ≤ log₂(2M), so the natural-log bound is the stronger of the two readings
--   - encoding: E_R max_f over the arbitrary phase function f → ∀ maps f : Oracle K N → ([M] → Bool) inside E_R; reason: a bound for every map R ↦ f_R is a bound on E_R max_f (finitely many f, so the maximum is attained)
--   - encoding: K keys, bound divided by K → hypothesis 1 ≤ K; reason: excludes only the empty key set, where E_k and the division by K are undefined
--   - generalization: N = 2^n and workspace dimension M = 2^m (§3, p.11) → any natural numbers N and M; reason: the powers of two are included; the bound is stated for the exact dimensions, and the proof does not use that they are powers of two
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 9.2, p.33 (PDF p.36); Definition 9.1, p.33

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Alg
import Definitions.Def_PreprocOWS_Supplement_searchWin
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Theorem 9.2 (One-query search bound for binary phase states, [DLM26, Theorem A.1])**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…),
p.33 (PDF p.36): for the oracle state search game associated with the family `{|ψ_{R,k}⟩}_{k∈[K]}` of
Definition 9.1, with `R = (R(k,x))` a family of independent Rademacher random variables, every
one-query adversary with workspace dimension `M` satisfies `E_R[Win(𝒜 | R)] ≤ 2(1 + log(2M))/K`.

**Formalization Note.** `log` is the natural logarithm (`Real.log`; the stronger of the readings
`ln`, `log₂`). The adversary is an isometry `V : ℂ^N → ℂ^M` and a projective measurement
`{Π_k}` on `ℂ^M`, both independent of `R`, and a phase function `f R : [M] → {±1}` depending
arbitrarily on `R` (the max over `f` inside `E_R` is `∀` maps `R ↦ f R`). `R` is uniform over
all sign functions on `[K] × [N]`; `K ≥ 1`. -/
theorem theorem_9_2 : ∀ (K N M : ℕ), 1 ≤ K →
    ∀ V : Matrix (Fin M) (Fin N) ℂ, IsIsometry V →
    ∀ P : Fin K → Matrix (Fin M) (Fin M) ℂ, IsProjMeas P →
    ∀ f : Oracle K N → Fin M → Bool,
      avg (fun R => searchWin V P (f R) R) ≤ 2 * (1 + Real.log (2 * M)) / K := by sorry

end PreprocOWS.Supplement
