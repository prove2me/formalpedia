-- Prove2me | Theorems.Thm_Polynomial_residuePower_cast
-- name    : Polynomial.residuePower_cast
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:44.359266+00:00
-- url     : https://prove2.me/theorems/ee9027a6-04d7-4dd0-bb8b-61a98b402497
-- title:
--   The residue-power algorithm computes ordinary modular exponentiation
-- statement:
--   Let $v,e,m∈ℕ$, and let $R(v,e,m)$ be the computed residue power. In $ℤ/mℤ$, $$R(v,e,m)=v^e.$$ This verifies the primitive modular-exponentiation routine used by the residue certificates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_Polynomial_BinomialResidue

set_option autoImplicit false
open Polynomial

theorem Polynomial.residuePower_cast (value exponent modulus : ℕ) :
    (residuePower value exponent modulus : ZMod modulus) =
      (value : ZMod modulus) ^ exponent := by sorry
