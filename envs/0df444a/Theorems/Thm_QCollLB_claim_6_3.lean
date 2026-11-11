-- Prove2me | Theorems.Thm_QCollLB_claim_6_3
-- name    : QCollLB.claim_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:02.778729+00:00
-- url     : https://prove2.me/theorems/571bfe41-7033-4f12-96c1-d90bb61bfe02
-- title:
--   Claim 6.3 — a uniform permutation induces the balanced distribution
-- statement:
--   Fix $k\ge2$, a public bucket map $b:[n]\to[N]$ with buckets of size $k$, and an injection $\iota:[N]\hookrightarrow\mathbb Z_q$. Then
--
--   1. $x^\pi\in X^\iota_{n,k}$ for every $\pi\in S_n$;
--   2. if $\pi$ is uniform on $S_n$, then $x^\pi$ is uniform on $X^\iota_{n,k}$: for every $x\in X^\iota_{n,k}$,
--   $$
--   \Pr_{\pi}[x^\pi=x]=\frac{|\{\pi:x^\pi=x\}|}{n!}=\frac1{|X^\iota_{n,k}|}.
--   $$
--
--   This lets a uniformly random permutation stand in for the balanced hard distribution of $k$-to-one inputs.
--
--   Differences from the source:
--   - encoding: "x^π is uniform on X" → every x ∈ X has probability |{π : x^π = x}|/n! = 1/|X|; reason: this is the definition of the uniform law; points outside X have probability 0 by clause 1
--   - encoding: a fixed public partition into buckets of size k with n = kN → any bucket map b : Fin n → Fin N whose fibres have size k; reason: a bucket map is exactly such a partition; it forces n = kN
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Claim 6.3, p.47

import Mathlib
import Definitions.Def_QCollLB_Buckets

namespace QCollLB

/-- **Claim 6.3 (The balanced distribution induced by a permutation)** (Peng–Wu,
arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Claim 6.3, p.47). For every public bucket map `b`
(buckets of size `k ≥ 2`) and injection `ι : [N] ↪ Z_q`, `x^π ∈ X^ι_{n,k}` for every `π ∈ S_n`; and if
`π` is uniform on `S_n`, then `x^π` is uniform on `X^ι_{n,k}`: every `x ∈ X^ι_{n,k}` has probability
`|{π : x^π = x}|/n! = 1/|X^ι_{n,k}|`.

**Formalization Note.** `k ≥ 2` is the paper's standing assumption (§2.1, p.13; Definition 5.23).
The bucket map has fibres of size `k`, which forces `n = kN`. -/
theorem claim_6_3 {n N q k : ℕ} [NeZero q] (hk : 2 ≤ k) (ι : Fin N ↪ ZMod q)
    (b : Fin n → Fin N) (hb : IsBucketMap k b) :
    (∀ π : Equiv.Perm (Fin n), xPi ι b π ∈ balancedSet k ι) ∧
      ∀ x ∈ balancedSet (n := n) k ι,
        ((Finset.univ.filter fun π : Equiv.Perm (Fin n) => xPi ι b π = x).card : ℝ) /
            (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
          1 / ((balancedSet (n := n) k ι).card : ℝ) := by sorry

end QCollLB
