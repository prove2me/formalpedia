-- Prove2me | Theorems.Thm_RuntimeTransfer_chirp_identity
-- name    : RuntimeTransfer.chirp_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:26.481547+00:00
-- url     : https://prove2.me/theorems/2bd524d7-f2e9-4a2a-9279-af9921d3845b
-- title:
--   Bluestein chirp identity for every length
-- statement:
--   For every natural $n$, nonzero complex $\rho$, and complex length-$n$ array $x$, decoding the middle product of the chirp arrays gives entries $\sum_{j=0}^{n-1}x_j(\rho^2)^{jk}$. Equivalently, $\rho^{k^2}\sum_j x_j\rho^{j^2}\rho^{-(k-j)^2}=\sum_j x_j(\rho^2)^{jk}$. Chirp exponents use integer subtraction and integer powers. No root-of-unity assumption is needed for this identity; the empty array is included.
-- source:
--   General runtime transfer and its Fourier/packing applications, companion proof note for this mission, 24 October 2026. Original cost-semantics formulation of standard substitution principles; not a claimed new complexity bound. Theorem 3, algebraic identity. Classical source: Bluestein (1970), https://doi.org/10.1109/TAU.1970.1162132, pp. 451–455.

import Definitions.Def_RuntimeTransferFourier
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.chirp_identity {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0) (x : Fin n → ℂ) :
    chirpDecode ρ (middleProduct (chirpQuery ρ x)) = fourierValue ρ x := by sorry
