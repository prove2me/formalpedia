-- Prove2me | Theorems.Thm_RandLatEnum_eq_4_5
-- name    : RandLatEnum.eq_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:30.646975+00:00
-- url     : https://prove2.me/theorems/c92884e5-235f-4e7e-a92b-b838f4bba822
-- title:
--   Eq. (4.5) — reversed dual-HKZ: $P_k\mapsto P_{d-k}$ and the reflected profile $p_D$
-- statement:
--   Let $L$ be a unimodular lattice of rank $d$ with basis $B$, and let $B_H$ be the reversal of the dual basis of $B$ (so that $B$ is obtained by reversing and dualizing $B_H$, a basis of the dual lattice $L^*$). Then:
--
--   1. for every $0\le k\le d$, $P_k(B)=P_{d-k}(B_H)$;
--   2. if $B_H$ is HKZ-reduced, then uniformly for $0\le t\le1$,
--   $$
--   \frac{P_{\lfloor td\rfloor}(B)}{d\ln d}\le p_D(t)+o(1),\qquad p_D(t)=p_H(1-t)=-\frac t2\ln t ,
--   $$
--   i.e. for every $\varepsilon>0$ there is $D$ such that for all $d\ge D$, all such bases and all $t\in[0,1]$, $P_{\lfloor td\rfloor}(B)\le(p_D(t)+\varepsilon)\,d\ln d$.
--
--   This controls the left block (reduced by reversed dual-HKZ) in the block-replacement step of the proof of Theorem 1.5.
--
--   **Formalization Note** "$B$ is the reversed dual of an HKZ basis of $L^*$" is written as "the reversal of the dual basis of $B$ is HKZ": dualizing twice returns the basis and reversal commutes with dualizing.
--
--   Differences from the source:
--   - generalization: a unimodular rank-d lattice (identified with ℝ^d) → the span of a linearly independent b : Fin d → ℝᵏ for any ambient k, with latticeDet b = 1; reason: the paper applies the bound to blocks living in subspaces; k = d is the printed case
--   - encoding: B = reversal of the dual of an HKZ basis B_H of L* → B_H := revBasis (dualBasis b) and IsReduced B_H; reason: dual of the dual basis is the basis and reversal commutes with dualizing, so the two descriptions give the same pairs (B, B_H)
--   - encoding: o(1), uniformly for 0 ≤ t ≤ 1 → ∀ ε > 0 ∃ D, one threshold for all d ≥ D, all bases and all t ∈ [0, 1]; reason: definition of a uniform o(1)
--   - generalization: the identity P_k ↦ P_{d−k} for the reversed dual of an HKZ basis of L* → P_j(B) = P_{d−j}(revBasis (dualBasis B)) for every basis B of a unimodular lattice (no HKZ hypothesis in clause (1)); reason: the identity is a Gram–Schmidt fact that uses only det = 1; HKZ bases are a special case
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §4.1, (4.5), p.19

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced
import Definitions.Def_RandLatEnum_prefixLogDet
import Definitions.Def_RandLatEnum_pD
import Definitions.Def_RandLatEnum_dualBasis
import Definitions.Def_RandLatEnum_revBasis

namespace RandLatEnum

open KannanLattice.Core

/-- **Eq. (4.5) (reversed dual-HKZ bases)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §4.1, (4.5), p.19).
"Reversing and dualizing an HKZ basis of the dual lattice changes the prefix determinant `P_k` to
`P_{d−k}`. The corresponding upper bound is therefore the reflected profile `p_D(t) = p_H(1 − t)`."
For a basis `B` of a unimodular rank-`d` lattice, write `B_H` for the reversal of its dual basis
(so `B` is obtained by reversing and dualizing `B_H`, a basis of `L*`). Then
(1) `P_k(B) = P_{d−k}(B_H)` for `0 ≤ k ≤ d`, and
(2) if `B_H` is HKZ, uniformly for `0 ≤ t ≤ 1`, `P_{⌊td⌋}(B)/(d ln d) ≤ p_D(t) + o(1)`.

**Formalization Note.** "`B` is the reversed dual of an HKZ basis `B_H` of `L*`" is written as
"`B_H := revBasis (dualBasis B)` is HKZ": the dual of the dual basis is the basis, and reversal
commutes with dualizing. A unimodular rank-`d` lattice is the span of a linearly independent
`b : Fin d → ℝᵏ` (any ambient `k`) with Gram–Schmidt product `1`. Uniformity as in Lemma 4.1. -/
theorem eq_4_5 :
    (∀ (d k : ℕ) (b : Fin d → EuclideanSpace ℝ (Fin k)),
      LinearIndependent ℝ b → latticeDet b = 1 →
      ∀ j : ℕ, j ≤ d → prefixLogDet b j = prefixLogDet (revBasis (dualBasis b)) (d - j)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ (k : ℕ) (b : Fin d → EuclideanSpace ℝ (Fin k)),
      LinearIndependent ℝ b → latticeDet b = 1 → IsReduced (revBasis (dualBasis b)) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        prefixLogDet b ⌊t * d⌋₊ / (d * Real.log d) ≤ pD t + ε := by sorry

end RandLatEnum
