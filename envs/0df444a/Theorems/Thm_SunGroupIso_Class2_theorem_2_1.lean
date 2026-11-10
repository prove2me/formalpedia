-- Prove2me | Theorems.Thm_SunGroupIso_Class2_theorem_2_1
-- name    : SunGroupIso.Class2.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:07:00.574654+00:00
-- url     : https://prove2.me/theorems/92f89f79-3501-4451-8574-59844f2381bf
-- title:
--   Theorem 2.1 — alternating matrix tuple isometry over Z/p^τZ and generators of its automorphism group
-- statement:
--   There is one constant $C$ such that: (decision) one Turing machine, for every prime $p$, all positive integers $\tau,n,m$ and all alternating $A,B\in M(n,\mathbb Z/p^\tau)^m$, on the code of $(p,\tau,n,m,A,B)$ outputs $1$ if some $P\in GL(n,\mathbb Z/p^\tau)$ has $P^TA_iP=B_i$ for all $i$ and $0$ otherwise, within $\lceil p^{C\tau n^{7/4}\log(\tau n+2)}\rceil\cdot(m+2)^C$ steps; (generators) one Turing machine, on the code of $(p,\tau,n,m,A)$, outputs within the same bound a list of at most $\lceil p^{C\tau n^{7/4}\log(\tau n+2)}\rceil\cdot(m+2)^C$ invertible matrices generating exactly the group $\{P\in GL(n,\mathbb Z/p^\tau):P^TA_iP=A_i\ \forall i\}$.
--
--   Differences from the source:
--   - encoding: an algorithm, no machine model fixed; inputs are groups, restrictions, tensors or matrix tuples → one Mathlib multi-stack Turing machine run through the published HMBinPacking.OutputsWithin, on binary codes built from the published encodeNat (groups by labelled Cayley tables, every labelling quantified); reason: Turing machines and RAMs simulate each other with polynomial overhead; any standard code differs polynomially
--   - reading: 'there is an algorithm … in time p^{O(·)}' (the O-constant and the algorithm unspecified in their dependence on p) → one machine and one constant C chosen before the prime p and every other input; reason: the paper presents 'a general algorithm that works for all the possible p-groups of class 2' (p. 8, PDF p. 10); the uniform reading is the stronger one
--   - reading: log(τ·n) → Real.log (τ·n + 2); reason: for τn ≥ 2, log(τn) ≤ log(τn+2) ≤ 2 log(τn), so the classes p^{O(·)} agree; at τ = n = 1 the printed exponent is 0 and the bound p^0 = 1 step cannot be met by any machine that reads its input
--   - encoding: poly(m) → (m+2)^C with the same constant C; reason: one polynomial; the +2 only matters at m ≤ 1
--   - encoding: real-valued bounds p^{x} → ⌈p^x⌉ in ℕ (ppow), natural logarithms; reason: step counts are natural numbers; rounding up changes no bound
--   - generalization: 'Throughout this paper, unless specified, we assume that all matrix tuples are non-degenerate' (p. 8, PDF p. 10) → no non-degeneracy hypothesis; reason: Appendix A (p. 58, PDF p. 60) removes it by preprocessing the common zero summands; a statement for all alternating inputs specializes to the non-degenerate ones
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Theorem 2.1, p. 9 (PDF p. 11)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SunGroupIso_Class2_Tensor

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Theorem 2.1** (c.f. Theorem 1.2 of [GIQS26]; Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Theorem 2.1, p. 9, PDF p. 11; proved in
Appendix A as Theorems A.1 and A.2). Let `R = Z/p^τZ` for any prime `p` and positive integer `τ`, and
`A, B ∈ M(n, R)^m` alternating. One algorithm decides whether some `P ∈ GL(n, R)` has `Pᵀ A P = B` in time
`p^{O(τ n^{7/4} log(τn))} · poly(m)`, and one algorithm outputs, in the same time, a generating set of size
`p^{O(τ n^{7/4} log(τn))} · poly(m)` of the invertible automorphism group `{P ∈ GL(n,R) : Pᵀ A P = A}`. -/
theorem theorem_2_1 :
    ∃ C : ℕ,
      (∃ M : Turing.TM2ComputableAux Bool Bool,
        ∀ (p τ n m : ℕ), p.Prime → 0 < τ → 0 < n → 0 < m →
        ∀ A B : Fin m → Matrix (Fin n) (Fin n) (ZMod (p ^ τ)),
          (∀ i, IsAltMat (A i)) → (∀ i, IsAltMat (B i)) →
          HMBinPacking.OutputsWithin M (encHeader p τ n m ++ encTuple A ++ encTuple B)
            [decide (Congruent A B)]
            (ppow p (C * τ * (n : ℝ) ^ ((7 : ℝ) / 4) * Real.log (τ * n + 2)) * (m + 2) ^ C)) ∧
      (∃ M : Turing.TM2ComputableAux Bool Bool,
        ∀ (p τ n m : ℕ), p.Prime → 0 < τ → 0 < n → 0 < m →
        ∀ A : Fin m → Matrix (Fin n) (Fin n) (ZMod (p ^ τ)), (∀ i, IsAltMat (A i)) →
          ∃ L : List (GL (Fin n) (ZMod (p ^ τ))),
            (Subgroup.closure {P | P ∈ L} : Set (GL (Fin n) (ZMod (p ^ τ)))) = autSet A ∧
            L.length ≤ ppow p (C * τ * (n : ℝ) ^ ((7 : ℝ) / 4) * Real.log (τ * n + 2)) * (m + 2) ^ C ∧
            HMBinPacking.OutputsWithin M (encHeader p τ n m ++ encTuple A)
              (encList (fun P : GL (Fin n) (ZMod (p ^ τ)) => encMat P.val) L)
              (ppow p (C * τ * (n : ℝ) ^ ((7 : ℝ) / 4) * Real.log (τ * n + 2)) * (m + 2) ^ C)) := by sorry

end SunGroupIso.Class2
