-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_comparator_invariant
-- name    : RelativisticZK205.ThreeCol.comparator_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:29.075002+00:00
-- url     : https://prove2.me/theorems/73a549b5-7e4a-48bd-87ff-26b5213a19ee
-- title:
--   Proof of Theorem 1 (p.11) — comparator invariant $x_k\oplus x'_k=\bigwedge_{m=1}^{k}(\bar i_m\oplus i'_m)$
-- statement:
--   Run the comparator of Step 4 with $S_1$ holding the label $i$ and $S_2$ the label $i'$: $x_1=\bar i_1$, $x'_1=i'_1$, and for each iteration two PR-boxes and the updates $x_{k+1}=(x_k\wedge\bar i_{k+1})\oplus y\oplus z$, $x'_{k+1}=(x'_k\wedge i'_{k+1})\oplus y'\oplus z'$. Then for every $k\ge1$ and on every outcome of the PR-boxes,
--
--   $$
--   x_k\oplus x'_k=\bigwedge_{m=1}^{k}(\bar i_m\oplus i'_m).
--   $$
--
--   So $x_k\oplus x'_k=1$ exactly when the first $k$ bits of $i$ and $i'$ agree. This is the induction behind Step 4.
--
--   Differences from the source:
--   - generalization: for 1 ≤ k ≤ h, with h-bit vertex labels → for every k ≥ 1 and all natural-number labels i, i′, with comparator k the run that stops at (x_k, x′_k); reason: the first k − 1 iterations do not depend on h or on the label width; taking k ≤ h and labels below 2^h gives the source's statement
--   - encoding: the m-th bit of a label, with bit positions starting at 1 → bit i (m − 1) = Nat.testBit i (m − 1), with the conjunction written using List.range k; reason: the source fixes no bit order; the first k least-significant bits implement the same k-bit comparison, with positions numbered from 0 in Lean
--   - encoding: an identity between the bits the simulators compute → the identity on every outcome of positive probability (the support of the output law); reason: an identity of random bits holds surely; for a discrete law this is exactly the support
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, proof of Theorem 1 ("We set x_k, x′_k so that …")

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Simulator

namespace RelativisticZK205.ThreeCol

/-- Proof of Theorem 1, p.11: the comparator of Step 4 keeps the invariant
`x_k ⊕ x'_k = ⋀_{m=1}^{k} (ī_m ⊕ i'_m)` for `1 ≤ k ≤ h`. Here `comparator k i i'` is the law of
`(x_k, x'_k)` reached after the first `k - 1` iterations of Step 4(b), and the `m`-th bit of a label
is `bit · (m - 1)`. The invariant holds on every outcome of positive probability. -/
theorem comparator_invariant (k : ℕ) (hk : 1 ≤ k) (i i' : ℕ) :
    ∀ p ∈ (comparator k i i').support,
      xor p.1 p.2 = (List.range k).all fun m => xor (!bit i m) (bit i' m) := by sorry

end RelativisticZK205.ThreeCol
