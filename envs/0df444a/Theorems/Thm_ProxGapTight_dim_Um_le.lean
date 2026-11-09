-- Prove2me | Theorems.Thm_ProxGapTight_dim_Um_le
-- name    : ProxGapTight.dim_Um_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:57:12.903363+00:00
-- url     : https://prove2.me/theorems/28a53c7d-ae05-461c-b675-18ff2a199136
-- title:
--   Proof of Theorem 3.1, p.13 — $\dim_{\mathbb F_p}U_m\le\binom{am+2a(p-1)}{2a(p-1)}$
-- statement:
--   Let $p$ be a prime, $Q=p^a$ and $m\ge0$. Then
--   $$
--   k_m=\dim_{\mathbb F_p}U_m\le\binom{am+2a(p-1)}{2a(p-1)},
--   $$
--   which is $O_{p,Q}(m^{2a(p-1)})$.
--
--   The dimension bound controls the size $q^{rk_m}$ of the union bound over $D_m$ and so fixes the exponent $D=2a(p-1)+1$ in the block-length condition $N\ge As^D$ of the main theorem.
--
--   **Formalization Note** $\mathbb F_Q$ is any field of order $p^a$; the explicit binomial bound is stated, and it implies the $O(\cdot)$ form for fixed $p,a$.
--
--   Differences from the source:
--   - generalization: m sufficiently large (context of the proof) → every m; reason: the evaluation-map argument works for every m
--   - generalization: F_Q → any field with Fintype.card = p ^ a; reason: all fields of that order are isomorphic to it; the statement specializes to it
--   - encoding: k_m ≤ binom(am + 2a(p − 1), 2a(p − 1)) = O_{p,Q}(m^{2a(p−1)}) → the binomial bound only; reason: for fixed p, a the binomial is a polynomial in m of degree 2a(p − 1), so the O-clause follows from it
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), proof of Theorem 3.1, p.13, display

import Mathlib
import Definitions.Def_ProxGapTight_Um

namespace ProxGapTight

/-- **Dimension of `U_m`**, proof of Theorem 3.1, Kominers, Thaler, Zheng, manuscript (Sept. 2026),
p.13, display: `k_m := dim_{F_p} U_m ≤ binom(am + 2a(p − 1), 2a(p − 1)) = O_{p,Q}(m^{2a(p−1)})`.

**Formalization Note.** `F_Q` is any field `K` of order `Q = p^a`; `F_p = ZMod p`. The explicit
binomial bound is stated; for fixed `p, a` it implies the `O_{p,Q}(m^{2a(p−1)})` clause. Stated
for every `m` (the paper's context is `m` large). -/
theorem dim_Um_le (p a m : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) :
    Module.finrank (ZMod p) (Um K m p) ≤
      Nat.choose (a * m + 2 * a * (p - 1)) (2 * a * (p - 1)) := by sorry

end ProxGapTight
