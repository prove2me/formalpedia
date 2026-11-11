-- Prove2me | Theorems.Thm_QCollLB_claim_6_5
-- name    : QCollLB.claim_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:47.791783+00:00
-- url     : https://prove2.me/theorems/56b794c5-d64f-499d-a419-4abe25a1c7db
-- title:
--   Claim 6.5 — the success events coincide
-- statement:
--   Fix $k\ge2$, a public bucket map $b$ with buckets of size $k$ and an injection $\iota:[N]\hookrightarrow\mathbb Z_q$. For every $\pi\in S_n$ and every $\rho\subseteq[n]$ with $|\rho|=k$:
--   $$
--   \rho\text{ is a }k\text{-collision of }x^\pi\iff \pi(\rho)=B_y\text{ for some }y\in[N].
--   $$
--
--   So Promised $k$-to-one Finding on $x^\pi$ and Permutation Bucket Finding on $\pi$ have the same valid outputs.
--
--   Differences from the source:
--   - encoding: a fixed public partition into buckets of size k → any bucket map b : Fin n → Fin N whose fibres have size k; reason: same objects
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Claim 6.5, p.48

import Mathlib
import Definitions.Def_QCollLB_OneRound
import Definitions.Def_QCollLB_Buckets

namespace QCollLB

/-- **Claim 6.5 (Equivalence of the success events)** (Peng–Wu, arXiv:2611.01767 (PDF sha256
4e5aba34…d9fc), Claim 6.5, p.48). For every `π ∈ S_n` and every `ρ ⊆ [n]` with `|ρ| = k`, `ρ` is a
valid output for Promised `k`-to-one Finding on `x^π` (a `k`-collision of `x^π`) if and only if it
is a valid output for Permutation Bucket Finding on `π` (`π(ρ) = B_y` for some `y`).

**Formalization Note.** `k ≥ 2` is the paper's standing assumption (§2.1, p.13); the bucket map has
fibres of size `k` (Definition 5.23). -/
theorem claim_6_5 {n N q k : ℕ} (hk : 2 ≤ k) (ι : Fin N ↪ ZMod q) (b : Fin n → Fin N)
    (hb : IsBucketMap k b) (π : Equiv.Perm (Fin n)) (ρ : Finset (Fin n)) (hρ : ρ.card = k) :
    IsKCollision k (xPi ι b π) ρ ↔ IsBucketFind k b π ρ := by sorry

end QCollLB
