-- Prove2me | Theorems.Thm_ToricFoliations_tail_coefficients_eq_one
-- name    : ToricFoliations.tail_coefficients_eq_one
-- status  : Open
-- author  : @hiraeth
-- created : 2026-10-07T12:32:13.779844+00:00
-- url     : https://prove2.me/theorems/ae656d1a-7e34-4f2d-ac17-dabb321f7823
-- title:
--   Claim — the tail coefficients are all equal to 1
-- statement:
--   **theorem_title:** Claim — the tail coefficients are all equal to 1
--
--   In the setting of Theorem 1.3, suppose the extremal ray $R$ satisfies
--   $l_{\mathscr F}(R)>r$ and let $C=V(W)$ be the torus-invariant curve of the
--   ray after the reordering (3.2). Let the tail indices be
--   $n-r+1,\dots,n+1$, i.e. the last $r+1$ indices of the wall relation. If each
--   tail vector $v_{n-r+1},\dots,v_{n+1}$ lies in $V$, then the corresponding
--   coefficients in the wall relation (3.1) are all equal to 1:
--
--   $$
--   a_{n-r+1}=\cdots=a_{n+1}=1.
--   $$
--
--   This is the Claim of the paper (between equations (3.9) and (3.10)); its
--   proof is a divisibility argument using the multiplicities of the cones
--   $\sigma_k$ and $\mu_{k,n+1}$.
--
--   **Formalization Note.** `tailIndex hr j` is the Lean index of
--   $v_{n-r+j}$ for `0 ≤ j ≤ r`; the hypothesis is that every
--   `toComplex (C.v (tailIndex hr j))` lies in `V`.
-- source:
--   Fujino--Sato 2024, A remark on toric foliations, Arch. Math. 122 (2024) 621--627, https://doi.org/10.1007/s00013-024-01991-1 (arXiv:2309.09461), Section 3, Claim after eq. (3.9)

import Mathlib
import Definitions.Def_ToricFoliations

open scoped BigOperators

namespace ToricFoliations

/--
The Claim in the proof of Theorem 1.3: in the long-ray case, once the tail
indices `n-r+1,...,n+1` (Lean: `tailIndex hr j`) are known to lie in `V`,
the wall relation forces
`a_{n-r+1} = ... = a_{n+1} = 1`.

This is the divisibility argument following equation (3.9) of the paper.
-/
theorem tail_coefficients_eq_one {n r : ℕ} (hr : r ≤ n) (C : WallData n)
    (V : Submodule ℂ (Complexified n))
    (hrank : Module.finrank ℂ V = r)
    (hlong : r < curveLength C V)
    (htail : ∀ j : Fin (r + 1), toComplex (C.v (tailIndex hr j)) ∈ V) :
    ∀ j : Fin (r + 1), C.a (tailIndex hr j) = 1 := by
  sorry

end ToricFoliations
