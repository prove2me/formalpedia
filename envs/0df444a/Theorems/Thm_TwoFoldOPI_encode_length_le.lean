-- Prove2me | Theorems.Thm_TwoFoldOPI_encode_length_le
-- name    : TwoFoldOPI.encode_length_le
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-10T20:11:41.592359+00:00
-- url     : https://prove2.me/theorems/1ee455f2-55ed-44fb-a852-581e490559c4
-- title:
--   The instance encoding of Theorem 7.4 has length polynomial in $m+r+q+t$
-- statement:
--   There are constants $a,b$ such that for every instance $x$ of Theorem 7.4 (field $\mathbb F_q=\mathbb F_p[X]/(f)$, an $r\times m$ matrix, a tag, $m$ forbidden values and a precision $t$) the public bit encoding satisfies
--   $$|\mathrm{enc}(x)|\le a\,(m+r+q+t+1)^b .$$
--
--   The encoding writes $p$, $\deg f$, the coefficients of $f$, $m$, $r$ and $t$ in self-delimiting binary, and $rm+m$ field elements with $\deg f\cdot\lceil\log_2p\rceil$ bits each. All these lengths are polynomial in $q=p^{\deg f}$, $m$, $r$ and $t$. So a running time polynomial in the size parameter $m+r+q+t$ also allows reading the whole encoding.
--
--   **Formalization Note.** `Input.scale x = m + r + F.q + t` with `F.q = p ^ natDegree f`.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held), §7.3, Theorem 7.4, p.40 ("running in poly(m, q, log(1/ϵ)) time") and §5.2 "Computational conventions", p.26; the encoding is TwoFoldOPI.Input.encode and the size parameter TwoFoldOPI.Input.scale.

import Mathlib
import Definitions.Def_TwoFoldOPI_Input

namespace TwoFoldOPI

theorem encode_length_le : ∃ a b : ℕ, ∀ x : Input, x.encode.length ≤ a * (x.scale + 1) ^ b := by
  sorry

end TwoFoldOPI
