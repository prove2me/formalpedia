-- Prove2me | Theorems.Thm_SaglamGV_exists_row_of_no_odd_circuit
-- name    : SaglamGV.exists_row_of_no_odd_circuit
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:49:07.626346+00:00
-- url     : https://prove2.me/theorems/35ae4e4c-04e5-4508-b3af-d6b84b14735e
-- title:
--   No odd circuit in $K$: a row $v$ with $v\mathbf K=\mathbf 1^\intercal$ gives a distance-$d$ code of size $\ge2^{n-m-1}$
-- statement:
--   Let $M\in\mathbb F_2^{m\times n}$ be such that $K=\{x\in B_d:Mx=0\}$ contains no odd circuit ($Z=0$). Then there is $v\in\mathbb F_2^n$ with
--
--   $$
--   v\cdot x=1\quad\text{for every }x\in K
--   $$
--
--   (that is, $v\mathbf K=\mathbf 1^\intercal$ for the matrix $\mathbf K$ whose columns are the elements of $K$), and the linear code $C=\ker\begin{pmatrix}M\\ v\end{pmatrix}$ has distance at least $d$ and $|C|\ge2^{n-m-1}$.
--
--   This is the step that turns "no odd circuit" into a code: one extra parity check removes every surviving low-weight word.
--
--   Differences from the source:
--   - generalization: the matrix M of §2 in the regime of §2 → every n, d, m and every M with Z = 0; reason: the linear-algebra argument uses only Z = 0
--   - encoding: |C| ≥ 2^{n−m−1} → 2^n ≤ 2^{m+1}·|C| in ℕ; reason: avoids natural-number subtraction; equivalent
--   - encoding: appending v to M; the code of a parity-check matrix → parityCode (appendRow M v), the kernel of the (m+1)×n matrix with last row v; reason: the code of a parity-check matrix is its kernel
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.3 ("It suffices to find a choice of M for which Z = 0 … Appending v to M then produces a parity-check matrix for a distance-d code"); §3.3, p.5 (size 2^{n−m−1})

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Circuit

namespace SaglamGV

/-- No odd circuit gives the extra parity-check row (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.3: "if K contains no odd circuit, then
every dependency among its elements has even cardinality. … Thus 1ᵀ lies in the row space of K, and
there is a row vector v satisfying vK = 1ᵀ. Appending v to M then produces a parity-check matrix for a
distance-d code"; the size $2^{n−m−1}$ is from §3.3, p.5).

If $K = \{x ∈ B_d : Mx = 0\}$ contains no odd circuit ($Z = 0$), there is $v ∈ 𝔽_2^n$ with
$v · x = 1$ for every $x ∈ K$, and the code with parity-check matrix $M$ extended by the row $v$
has distance at least $d$ and at least $2^{n−m−1}$ codewords.

**Formalization Note** $|C| ≥ 2^{n−m−1}$ is written $2^n ≤ 2^{m+1}|C|$ to avoid natural-number
subtraction. -/
theorem exists_row_of_no_odd_circuit (n d m : ℕ) (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (hZ : oddCircuitCount d M = 0) :
    ∃ v : Fin n → ZMod 2, (∀ x ∈ kerSet d M, dot v x = 1) ∧
      HasDistAtLeast (parityCode (appendRow M v)) d ∧
      2 ^ n ≤ 2 ^ (m + 1) * Nat.card (parityCode (appendRow M v)) := by sorry

end SaglamGV
