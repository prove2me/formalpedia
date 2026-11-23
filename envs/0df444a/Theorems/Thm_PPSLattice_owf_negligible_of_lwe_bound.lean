-- Prove2me | Theorems.Thm_PPSLattice_owf_negligible_of_lwe_bound
-- name    : PPSLattice.owf_negligible_of_lwe_bound
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:54.317275+00:00
-- url     : https://prove2.me/theorems/3682bb7a-9298-4cf3-9500-d8d4295e0ad2
-- title:
--   LWE distinguishing bounds give negligible inversion probability
-- statement:
--   Let $f$ be a candidate one-way function and suppose LWE is hard for the family $(q,\chi)$. Assume that, for every valid uniform inverter $I$, there are a polynomial-time computable sample count $m$, a valid uniform LWE distinguisher $D$, and a negligible function $\nu$ such that, at every dimension $n$,
--   $$
--   \Pr_{x\leftarrow\{0,1\}^n}[f(I(1^n,f(x)))=f(x)]
--    \le \left|\Pr[D=1\mid\mathrm{LWE}]-\Pr[D=1\mid\mathrm{uniform}]\right|+\nu(n).
--   $$
--   Then the inversion probability of $f$ against every valid uniform inverter is negligible.
--
--   This isolates the asymptotic bookkeeping in the LWE-to-one-way-function bridge: the remaining construction only has to establish a pointwise bound by one LWE advantage and a statistical error.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, Assumption 3.4, p.17; Theorems 4.3 and 4.5, pp.19–20. Extracted supporting lemma for the standard LWE-to-one-way-function implication used by Corollary 4.30, p.31.

import Mathlib
import Definitions.Def_PPSLattice_LWEHard
import Definitions.Def_PPSLattice_OWFInvProb
import Definitions.Def_PPSLattice_PolyTimeOn

set_option autoImplicit false
open QAlgorithms.Complexity

namespace PPSLattice

theorem owf_negligible_of_lwe_bound (q χ : ℕ → ℕ) (hLWE : LWEHard q χ)
    (f : Str → Str)
    (hbound : ∀ I : RestrictedDec.Adversary, I.Valid →
      ∃ m : ℕ → ℕ, PolyTimeOn (fun n : ℕ => encNat n) (fun n => encNat (m n)) ∧
        ∃ D : RestrictedDec.Adversary, D.Valid ∧
          ∃ ν : ℕ → ℝ, NoisyOWMPC.Negligible ν ∧
            ∀ n, owfInvProb f I n ≤
              |lweDistProb q χ m D n true - lweDistProb q χ m D n false| + ν n) :
    ∀ I : RestrictedDec.Adversary, I.Valid →
      NoisyOWMPC.Negligible (owfInvProb f I) := by sorry
