-- Prove2me | Theorems.Thm_PPSLattice_lwe_regime_one_way_candidate
-- name    : PPSLattice.lwe_regime_one_way_candidate
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:50:07.687114+00:00
-- url     : https://prove2.me/theorems/2b5f38df-a418-468f-bd0c-4e4c22262887
-- title:
--   The finite-coin LWE one-way candidate and its inversion-to-distinguishing reduction
-- statement:
--   Fix an exponent $0<\varepsilon$ and an LWE parameter family $(q,\chi)$ in the sub-exponential modulus-to-noise regime. There exists a polynomial-time computable candidate one-way function $f$, constructed from the LWE map and a finite-coin approximation of its error sampler, with the following inversion-to-distinguishing reduction.
--
--   For every valid uniform PPT inverter $I$, there are a polynomial-time computable sample count $m$, a valid uniform PPT distinguisher $D$, and a negligible statistical error $\nu$ such that, for every dimension $n$,
--   $$
--   \Pr_{x\leftarrow\{0,1\}^n}[f(I(1^n,f(x)))=f(x)]
--    \le \left|\Pr[D=1\mid\mathrm{LWE}]-\Pr[D=1\mid\mathrm{uniform}]\right|+\nu(n).
--   $$
--   The candidate is a deterministic finite-coin realization of $(\mathbf A,\mathbf s,\mathbf e)\mapsto(\mathbf A,\mathbf s^\top\mathbf A+\mathbf e)$, with suitable binary parsing and padding. The distinguisher runs the inverter on its challenge and tests the purported preimage; the negligible term accounts for the random world and for approximating the discrete Gaussian by finitely many fair coins.
--
--   This is the algorithmic and probabilistic core of the standard implication from LWE hardness to uniform one-way functions.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, Assumption 3.4, p.17; §4.3, p.20 (polynomial-time binary parameter computation); Corollary 4.30, p.31. Standard LWE-to-one-way-function construction specialized to the mission's uniform finite-coin machine model; extracted supporting obligation for Theorems 4.3 and 4.5, pp.19–20.

import Mathlib
import Definitions.Def_PPSLattice_LWERegime
import Definitions.Def_PPSLattice_LWEHard
import Definitions.Def_PPSLattice_OWFInvProb
import Definitions.Def_PPSLattice_PolyTimeOn

set_option autoImplicit false
open QAlgorithms.Complexity

namespace PPSLattice

theorem lwe_regime_one_way_candidate (ε : ℝ) (q χ : ℕ → ℕ)
    (hε : 0 < ε) (hreg : LWERegime ε q χ) :
    ∃ f : Str → Str, PolyTimeComputable f ∧
      ∀ I : RestrictedDec.Adversary, I.Valid →
        ∃ m : ℕ → ℕ, PolyTimeOn (fun n : ℕ => encNat n) (fun n => encNat (m n)) ∧
          ∃ D : RestrictedDec.Adversary, D.Valid ∧
            ∃ ν : ℕ → ℝ, NoisyOWMPC.Negligible ν ∧
              ∀ n, owfInvProb f I n ≤
                |lweDistProb q χ m D n true - lweDistProb q χ m D n false| + ν n := by sorry
