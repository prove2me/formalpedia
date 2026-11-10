-- Prove2me | Theorems.Thm_SunGroupIso_Class2_theorem_5_1
-- name    : SunGroupIso.Class2.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:07:16.122105+00:00
-- url     : https://prove2.me/theorems/e19b5b87-3c41-4172-b6ad-25017f9b7db9
-- title:
--   Theorem 5.1 — group restriction isomorphism in time p^{O(max{τn^{7/4}δ^{7/2}log(τn), τn^{3/2}δ^7 log(τn), nζ})}
-- statement:
--   There are one Turing machine $M$ and one constant $C$ such that for every prime $p$, all labelled finite $p$-groups $G,H$ of class 2 of order $p^n$, $n\ge1$, and all group restrictions $r$ of $G$ and $r'$ of $H$ with common parameters $\zeta,\gamma,\kappa,\tau,\delta$: $M$, on the two Cayley tables and the codes of the restrictions, outputs $1$ if there is a group restriction isomorphism from $G$ to $H$ and $0$ otherwise, within $\lceil p^{C\max\{\tau n^{7/4}\delta^{7/2}\log(\tau n+2),\ \tau n^{3/2}\delta^7\log(\tau n+2),\ n\zeta\}}\rceil$ steps.
--
--   Differences from the source:
--   - encoding: an algorithm, no machine model fixed; inputs are groups, restrictions, tensors or matrix tuples → one Mathlib multi-stack Turing machine run through the published HMBinPacking.OutputsWithin, on binary codes built from the published encodeNat (groups by labelled Cayley tables, every labelling quantified); reason: Turing machines and RAMs simulate each other with polynomial overhead; any standard code differs polynomially
--   - reading: 'there is an algorithm … in time p^{O(·)}' (the O-constant and the algorithm unspecified in their dependence on p) → one machine and one constant C chosen before the prime p and every other input; reason: the paper presents 'a general algorithm that works for all the possible p-groups of class 2' (p. 8, PDF p. 10); the uniform reading is the stronger one
--   - reading: two group restrictions (Problem 4.3) → two restrictions with the same parameters ζ, γ, κ, τ, δ; reason: restriction isomorphism compares z_i with z'_i, g_i with g'_i and ρ with ρ' coordinatewise, and condition 1 of p. 13 assumes the parameters equal
--   - reading: log(τ·n) → Real.log (τ·n + 2); reason: for τn ≥ 2, log(τn) ≤ log(τn+2) ≤ 2 log(τn), so the classes p^{O(·)} agree; at τ = n = 1 the printed exponent is 0 and the bound p^0 = 1 step cannot be met by any machine that reads its input
--   - encoding: real-valued bounds p^{x} → ⌈p^x⌉ in ℕ (ppow), natural logarithms; reason: step counts are natural numbers; rounding up changes no bound
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Theorem 5.1, p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_GroupIsoPoly_encPair
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SunGroupIso_Class2_Restriction

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Theorem 5.1** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Theorem 5.1, p. 26, PDF p. 28). For two group restrictions of two finite `p`-groups
of class 2 of order `p^n`, `n ≥ 1`, an algorithm solves the group restriction isomorphism problem in time
`p^{O(max{τ n^{7/4}δ^{7/2} log(τn), τ n^{3/2}δ^7 log(τn), nζ})}`. -/
theorem theorem_5_1 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (p n N : ℕ) (G H : Type) [Group G] [Group H] [Finite G] [Finite H]
        (eG : G ≃ Fin N) (eH : H ≃ Fin N) {ζ γ κ τ δ : ℕ}
        (r : Restriction G p ζ γ κ τ) (r' : Restriction H p ζ γ κ τ),
        p.Prime → IsPGroupClass2 p G → IsPGroupClass2 p H → Nat.card G = p ^ n → 0 < n →
        IsRestriction p δ r → IsRestriction p δ r' →
        let inp : List Bool := encPair N (cayley eG) (cayley eH) ++ encRestriction eG δ r ++
          encRestriction eH δ r'
        HMBinPacking.OutputsWithin M inp [decide (∃ f : G ≃* H, IsRestrictionIso r r' f)]
          (ppow p (C * max (max ((τ : ℝ) * (n : ℝ) ^ ((7 : ℝ) / 4) * (δ : ℝ) ^ ((7 : ℝ) / 2) *
              Real.log (τ * n + 2)) ((τ : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) * (δ : ℝ) ^ 7 *
              Real.log (τ * n + 2))) ((n : ℝ) * ζ))) := by sorry

end SunGroupIso.Class2
