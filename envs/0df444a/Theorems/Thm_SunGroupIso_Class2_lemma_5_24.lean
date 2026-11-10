-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_5_24
-- name    : SunGroupIso.Class2.lemma_5_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:09:10.444221+00:00
-- url     : https://prove2.me/theorems/0b300f4b-1c1e-411c-8a12-b85dcb9a7f87
-- title:
--   Lemma 5.24 — the extended vector matching algorithm
-- statement:
--   There are one Turing machine $M$ and one constant $C$ such that for every prime $p$, all labelled finite $p$-groups $G,H$ of class 2 of order $p^n$ ($n\ge1$) and all group restrictions of them with common parameters satisfying the standing assumptions of Section 5, including nontrivial specified central cyclic factors, with $T=\lceil p^{C\tau\log(\tau n+2)\max\{n^{7/4}\delta^{7/2},n^{3/2}\delta^7\}}\rceil$: if the restrictions have no matching extended vectors, $M$ outputs $0$ within $T$ steps; if they have, $M$ outputs within $T$ steps $1$, extended vectors $\vec b$ (of $G$'s restriction) and $\vec a'$ (of $H$'s) that match, and a list $\Gamma_1$ of at most $\lceil p^{C\tau n^{7/4}\delta^{7/2}\log(\tau n+2)}\rceil$ invertible matrices generating exactly the group of invertible $Q$ with $Q^TDQ=D$ for every matrix $D$ of the doubling $D'$ of the Matrix Tuple Construction of $\vec a'$ and $Q[m,m]=1$.
--
--   Differences from the source:
--   - encoding: an algorithm, no machine model fixed; inputs are groups, restrictions, tensors or matrix tuples → one Mathlib multi-stack Turing machine run through the published HMBinPacking.OutputsWithin, on binary codes built from the published encodeNat (groups by labelled Cayley tables, every labelling quantified); reason: Turing machines and RAMs simulate each other with polynomial overhead; any standard code differs polynomially
--   - reading: 'there is an algorithm … in time p^{O(·)}' (the O-constant and the algorithm unspecified in their dependence on p) → one machine and one constant C chosen before the prime p and every other input; reason: the paper presents 'a general algorithm that works for all the possible p-groups of class 2' (p. 8, PDF p. 10); the uniform reading is the stronger one
--   - reading: the standing assumptions of Section 5 ('we may assume', pp. 13–14; (7), p. 31; τ ≥ 2 in the proof of Lemma 5.15); reindexing with all remaining z_i of order p (PDF 29) → hypothesis Sec5Standing r r' (ψ, η equal, Y ≅ X, quotients isomorphic, ord(z_i) = ord(z'_i), ord(g̃_i) = ord(g̃'_i), equal z-coefficients of [g_i,g_j] and g_i^{ord(g̃_i)} for i, j ≤ γ, τ ≥ 2); p ≤ ord(z_i); reason: these are source standing assumptions; the positive cyclic orders prevent a zero denominator ord(z_i)/p
--   - reading: two group restrictions (Problem 4.3) → two restrictions with the same parameters ζ, γ, κ, τ, δ; reason: restriction isomorphism compares z_i with z'_i, g_i with g'_i and ρ with ρ' coordinatewise, and condition 1 of p. 13 assumes the parameters equal
--   - reading: log(τ·n) → Real.log (τ·n + 2); reason: for τn ≥ 2, log(τn) ≤ log(τn+2) ≤ 2 log(τn), so the classes p^{O(·)} agree; at τ = n = 1 the printed exponent is 0 and the bound p^0 = 1 step cannot be met by any machine that reads its input
--   - reading: 'Γ_1 with size p^{τ·n^{7/4}·δ^{7/2} log(τ·n)}' (no O on p. 49) → Γ_1.length ≤ ⌈p^{C·τ·n^{7/4}·δ^{7/2}·log(τn+2)}⌉; reason: obvious typo: the size comes from Theorem 2.1 (p^{O(·)}·poly(m)) and the proof of Theorem 5.1 restates it as p^{O(τ·n^{7/4}·δ^{7/2} log(τ·n))}; recorded as insight I3
--   - encoding: real-valued bounds p^{x} → ⌈p^x⌉ in ℕ (ppow), natural logarithms; reason: step counts are natural numbers; rounding up changes no bound
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 5.24, p. 49 (PDF p. 51)

import Mathlib
import Definitions.Def_GroupIsoPoly_encPair
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SunGroupIso_Class2_Tensor
import Definitions.Def_SunGroupIso_Class2_MatrixTuple

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 5.24** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 5.24, p. 49, PDF p. 51). Given group restrictions of two finite `p`-groups
`G, H` of class 2 of order `p^n` (under the standing assumptions of Section 5), an algorithm decides whether
they have extended vectors that match, in time `p^{O(τ log(τn) max{n^{7/4}δ^{7/2}, n^{3/2}δ^7})}`; if they do, it
outputs matching extended vectors `b⃗` (for `G`) and `a⃗'` (for `H`) and a generating set `Γ_1` of size
`p^{O(τ n^{7/4}δ^{7/2} log(τn))}` of the invertible automorphisms `Q` of the doubled tuple `D'` of `a⃗'` with
`Q[m, m] = 1`. -/
theorem lemma_5_24 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (p n N : ℕ) (G H : Type) [Group G] [Group H] [Finite G] [Finite H]
        (eG : G ≃ Fin N) (eH : H ≃ Fin N) {ζ γ κ τ δ : ℕ}
        (r : Restriction G p ζ γ κ τ) (r' : Restriction H p ζ γ κ τ),
        p.Prime → IsPGroupClass2 p G → IsPGroupClass2 p H → Nat.card G = p ^ n → 0 < n →
        IsRestriction p δ r → IsRestriction p δ r' → Sec5Standing r r' →
        let inp : List Bool := encPair N (cayley eG) (cayley eH) ++ encRestriction eG δ r ++
          encRestriction eH δ r'
        let T : ℕ := ppow p (C * τ * Real.log (τ * n + 2) *
            max ((n : ℝ) ^ ((7 : ℝ) / 4) * (δ : ℝ) ^ ((7 : ℝ) / 2))
              ((n : ℝ) ^ ((3 : ℝ) / 2) * (δ : ℝ) ^ 7))
        ((¬ ∃ (k : ℕ) (a : Fin k → G) (b : Fin k → H), IsExtVec r a ∧ IsExtVec r' b ∧ Matches r a r' b) →
          HMBinPacking.OutputsWithin M inp [false] T) ∧
        ((∃ (k : ℕ) (a : Fin k → G) (b : Fin k → H), IsExtVec r a ∧ IsExtVec r' b ∧ Matches r a r' b) →
          ∃ (k : ℕ) (b : Fin k → G) (a' : Fin k → H)
            (Γ1 : List (GL (Fin (doubling (mtc r' a')).size) (ZMod (p ^ τ)))),
            IsExtVec r b ∧ IsExtVec r' a' ∧ Matches r b r' a' ∧
            (Subgroup.closure {P | P ∈ Γ1} : Set (GL (Fin (doubling (mtc r' a')).size) (ZMod (p ^ τ)))) =
              normIsoSet (doubling (mtc r' a')) (mtc r' a').size ∧
            Γ1.length ≤ ppow p (C * τ * (n : ℝ) ^ ((7 : ℝ) / 4) * (δ : ℝ) ^ ((7 : ℝ) / 2) *
              Real.log (τ * n + 2)) ∧
            HMBinPacking.OutputsWithin M inp
              ([true] ++ encVec (encElem eG) b ++ encVec (encElem eH) a' ++
                encList (fun P : GL (Fin (doubling (mtc r' a')).size) (ZMod (p ^ τ)) => encMat P.val) Γ1)
              T) := by sorry

end SunGroupIso.Class2
