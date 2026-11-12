-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_theorem_3_2
-- name    : ReadOnceParityBP.LowerBound.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:54.918366+00:00
-- url     : https://prove2.me/theorems/b31e8ab8-d03e-42fa-a261-3b29a462694f
-- title:
--   Theorem 3.2 — uniform polynomial-time exact counting
-- statement:
--   There exists one deterministic finite Turing machine M and one polynomial p with natural coefficients such that, on every Boolean input list z, M writes the binary encoding of countInput(z) within p(|z|) actual machine steps. For z consisting of two n-bit blocks x,y with n even, its exact output is
--
--   $$\#\{B\subseteq\{0,\ldots,n-1\}:|B|=n/2,\ B\text{ is x-valid and y-eligible}\}.$$
--
--   This returns the integer count, including its output bits, and supplies the uniform algorithmic content needed for explicitness. It is stronger than computing only parity or charging only arithmetic operations.
--
--   **Formalization Note** M is Mathlib's bundled finite TM2 with its step relation and polynomial evaluated at the raw Boolean input length. The function body is the semantic count, not a presumed efficient algorithm.
--
--   Differences from the source:
--   - encoding: input pair of n-bit vectors with n even and exact integer output → x followed by y on a Boolean list, binary natural output, and zero on other lengths; reason: one total input/output convention states uniform computation and charges addressing, arithmetic, and writing the result; the empty valid input returns one
--   - generalization: positive even cycle lengths → also the empty cycle n=0; reason: the unique half-subset is empty; its canonical matching is empty and the exact count is one
--   - encoding: cycle positions Zₙ and two n-variable blocks → Fin n for the positions and Fin n ⊕ Fin n for the variables; reason: this retains exactly 2n distinct variables and the ordinary representative order for positive even n
--   - encoding: a polynomial-time algorithm for exact counting → Nonempty of Mathlib TM2ComputableInPolyTime for the fixed countInput function; reason: one finite machine and one polynomial bound its actual steps uniformly over all inputs; finite control and finite reachable alphabets give the usual polynomial-time Turing model
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Theorem 3.2 p.9, proof pp.9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_Explicit

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Theorem 3.2 (p. 9): there is a polynomial-time algorithm that, given
`(x, y) ∈ {0,1}^n × {0,1}^n` (`n` even), computes the number of `x`-valid and `y`-eligible sets
`B ⊆ ℤ_n` with `|B| = n/2`. The algorithm is a single Mathlib multi-stack Turing machine
reading the `2n` bits `x_0 … x_{n-1} y_0 … y_{n-1}` and writing the count in binary, within a
fixed polynomial number of steps in the input length. -/
theorem theorem_3_2 :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      Computability.encodingNatBool.encode countInput) := by sorry

end ReadOnceParityBP.LowerBound
