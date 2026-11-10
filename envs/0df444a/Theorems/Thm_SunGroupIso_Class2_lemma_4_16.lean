-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_4_16
-- name    : SunGroupIso.Class2.lemma_4_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:07:00.406211+00:00
-- url     : https://prove2.me/theorems/ced39ecc-6d4b-4e21-8e1c-333763db825d
-- title:
--   Lemma 4.16 — reduction of class-2 isomorphism to restricted group isomorphism
-- statement:
--   There are one Turing machine $M$ and one constant $C$ such that for every prime $p$, all labelled $p$-groups $G,H$ of class 2 of order $p^n$ and positive integers $\delta,\tau$ with $\tau\ge\delta+2$, writing $B=n/\delta+n\delta/\tau+\delta^3n^{4/9}(\log p)^2$ and $K=\lceil p^{C(n^{17/9}(\log p)^{8/9}+nB)}\rceil$ (the bound (4)): $M$, on the two Cayley tables, $\delta$ and $\tau$, outputs within $K$ steps a list of at most $K$ pairs of group restrictions $(r,r')$ of $G$ and $H$ with common parameters, $\zeta,\gamma\le CB$ and $\kappa\le(n+1)^C$, such that $G\cong H$ if and only if some listed pair is restriction-isomorphic.
--
--   Differences from the source:
--   - encoding: an algorithm, no machine model fixed; inputs are groups, restrictions, tensors or matrix tuples → one Mathlib multi-stack Turing machine run through the published HMBinPacking.OutputsWithin, on binary codes built from the published encodeNat (groups by labelled Cayley tables, every labelling quantified); reason: Turing machines and RAMs simulate each other with polynomial overhead; any standard code differs polynomially
--   - reading: 'there is an algorithm … in time p^{O(·)}' (the O-constant and the algorithm unspecified in their dependence on p) → one machine and one constant C chosen before the prime p and every other input; reason: the paper presents 'a general algorithm that works for all the possible p-groups of class 2' (p. 8, PDF p. 10); the uniform reading is the stronger one
--   - reading: 'reduce the group isomorphism problem … to K instances of restricted group isomorphism' → output a list of at most K valid restriction pairs such that G ≅ H iff some listed pair is restriction-isomorphic; reason: the meaning of a many-one (truth-table OR) reduction, as the proof of the lemma establishes it
--   - encoding: κ = poly(n) → κ ≤ (n+1)^C; reason: one polynomial, with the same constant C
--   - encoding: real-valued bounds p^{x} → ⌈p^x⌉ in ℕ (ppow), natural logarithms; reason: step counts are natural numbers; rounding up changes no bound
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.16, p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_GroupIsoPoly_encPair
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SunGroupIso_Class2_Restriction

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 4.16** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.16, p. 26, PDF p. 28). Given two `p`-groups of class 2 of order `p^n`
and positive integers `δ, τ` with `τ ≥ δ + 2`, an algorithm reduces their isomorphism problem to
`p^{O(n^{17/9}(log p)^{8/9} + n(n/δ + nδ/τ + δ^3 n^{4/9}(log p)^2))}` (4) instances of restricted group isomorphism
with `ζ, γ = O(n/δ + nδ/τ + δ^3 n^{4/9}(log p)^2)` and `κ = poly(n)`, in time (4): the groups are isomorphic
if and only if some produced pair of group restrictions is restriction-isomorphic. -/
theorem lemma_4_16 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (p n N : ℕ) (G H : Type) [Group G] [Group H] [Finite G] [Finite H]
        (eG : G ≃ Fin N) (eH : H ≃ Fin N) (δ τ : ℕ),
        p.Prime → IsPGroupClass2 p G → IsPGroupClass2 p H → Nat.card G = p ^ n → 0 < δ → δ + 2 ≤ τ →
        let B : ℝ := (n : ℝ) / δ + (n : ℝ) * δ / τ + (δ : ℝ) ^ 3 * (n : ℝ) ^ ((4 : ℝ) / 9) * Real.log p ^ 2
        let K : ℕ := ppow p (C * ((n : ℝ) ^ ((17 : ℝ) / 9) * Real.log p ^ ((8 : ℝ) / 9) + n * B))
        let inp : List Bool := encPair N (cayley eG) (cayley eH) ++ encUnary δ ++ encUnary τ
        ∃ L : List (Σ ζ γ κ : ℕ, Restriction G p ζ γ κ τ × Restriction H p ζ γ κ τ),
          L.length ≤ K ∧
          (∀ (ζ γ κ : ℕ) (r : Restriction G p ζ γ κ τ) (r' : Restriction H p ζ γ κ τ), ⟨ζ, γ, κ, r, r'⟩ ∈ L →
            IsRestriction p δ r ∧ IsRestriction p δ r' ∧
              (ζ : ℝ) ≤ C * B ∧ (γ : ℝ) ≤ C * B ∧ κ ≤ (n + 1) ^ C) ∧
          (Nonempty (G ≃* H) ↔
            ∃ (ζ γ κ : ℕ) (r : Restriction G p ζ γ κ τ) (r' : Restriction H p ζ γ κ τ), ⟨ζ, γ, κ, r, r'⟩ ∈ L ∧ ∃ f : G ≃* H, IsRestrictionIso r r' f) ∧
          HMBinPacking.OutputsWithin M inp
            (encList (fun x => encRestriction eG δ x.2.2.2.1 ++ encRestriction eH δ x.2.2.2.2) L)
            (K) := by sorry

end SunGroupIso.Class2
