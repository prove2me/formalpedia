-- Prove2me | Theorems.Thm_Polynomial_binomialBlocksResidue_cast
-- name    : Polynomial.binomialBlocksResidue_cast
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:33.644212+00:00
-- url     : https://prove2.me/theorems/dda5b8f4-6b79-456d-b8d0-c7dac3cfd5be
-- title:
--   The blockwise residue computation equals polynomial evaluation modulo $b^N$
-- statement:
--   Let $b,N∈ℕ$ with $b>0$, let $\mathcal B$ be a list of lists of exponents, let $R(b,N,\mathcal B)$ be the blockwise residue computation, and let $P_{\mathcal B}$ be the associated product of binomial blocks. In $ℤ/b^Nℤ$, $$R(b,N,\mathcal B)=P_{\mathcal B}(b).$$ This connects the efficient residue algorithm to exact polynomial evaluation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_Polynomial_BinomialResidue

set_option autoImplicit false
open Polynomial

theorem Polynomial.binomialBlocksResidue_cast (base count : ℕ) (hb : 0 < base)
    (blocks : List (List ℕ)) :
    (binomialBlocksResidue base count blocks : ZMod (base ^ count)) =
      (binomialBlocksPolynomial blocks).eval₂ (Int.castRingHom (ZMod (base ^ count)))
        (base : ZMod (base ^ count)) := by sorry
