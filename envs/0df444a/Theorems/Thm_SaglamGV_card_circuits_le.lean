-- Prove2me | Theorems.Thm_SaglamGV_card_circuits_le
-- name    : SaglamGV.card_circuits_le
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:49:05.39429+00:00
-- url     : https://prove2.me/theorems/c9af06f2-3af8-4c46-8dcd-92667a7fb242
-- title:
--   Circuit count $|\mathbb C_\ell|\le (V^\ell/\ell!)\,p_\ell$
-- statement:
--   For every $\ell$, the number of $\ell$-element circuits contained in $B_d$ satisfies
--
--   $$
--   |\mathbb C_\ell|\le\frac{V^\ell}{\ell!}\,p_\ell ,
--   $$
--
--   where $p_\ell=\Pr[X_1+\dots+X_\ell=0]$ for $X_i$ i.i.d. uniform on $B_d$. Each circuit sums to zero and yields $\ell!$ distinct ordered tuples counted by $V^\ell p_\ell$.
--
--   Differences from the source:
--   - generalization: the identity inside the standing regime ln n ≪ w ≤ (1/2 − ε)n of §2 → every n, d and ℓ; reason: the statement is an exact combinatorial/probabilistic identity or bound that does not use the regime; it specializes to the paper's case
--   - encoding: p_ℓ = Pr[X_1 + ⋯ + X_ℓ = 0] for X_i i.i.d. with law µ → zeroSumProb: the number of ordered ℓ-tuples in B_d^ℓ summing to 0, divided by V^ℓ; reason: µ is uniform on B_d, so the probability is this ratio; same values
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.2 (display |C_ℓ| ≤ V^ℓ p_ℓ/ℓ!)

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Circuit
import Definitions.Def_SaglamGV_Walk

namespace SaglamGV

/-- The circuit count $|C_ℓ| ≤ (V^ℓ/ℓ!) p_ℓ$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.2: "Every circuit in C_ℓ gives ℓ! distinct
ordered tuples counted by this event. Hence |C_ℓ| ≤ (V^ℓ/ℓ!) p_ℓ").

**Formalization Note** $p_ℓ$ is `zeroSumProb`, the number of ordered $ℓ$-tuples of elements of
$B_d$ summing to $0$ divided by $V^ℓ$. The bound is stated for every $n, d, ℓ$. -/
theorem card_circuits_le (n d ℓ : ℕ) :
    ((circuits n d ℓ).card : ℝ) ≤ (vol n d : ℝ) ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ := by sorry

end SaglamGV
