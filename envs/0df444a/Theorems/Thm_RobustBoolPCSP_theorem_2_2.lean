-- Prove2me | Theorems.Thm_RobustBoolPCSP_theorem_2_2
-- name    : RobustBoolPCSP.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:56.585313+00:00
-- url     : https://prove2.me/theorems/14132103-75cb-4ae7-817a-d405f035d7fb
-- title:
--   Theorem 2.2 (Bounded fixing sets or parity) — a perfect integrality gap for every finite Boolean template
-- statement:
--   Let $\Gamma$ be a finite Boolean template (not necessarily symmetric). Suppose there is a constant $C$ such that every folded idempotent polymorphism $F:\{0,1\}^L\to\{0,1\}$ of $\Gamma$, of every arity $L$, either is an odd parity or has a fixing set of size at most $C$. Then
--
--   $$\mathrm{fiPCSP}(\Gamma)\ \text{has a perfect integrality gap.}$$
--
--   Here $F$ is folded if $F(\mathbf 1-x)=1-F(x)$ and idempotent if $F(0^L)=0$, $F(1^L)=1$. This obstruction is the negative engine of the dichotomy.
--
--   Differences from the source:
--   - encoding: relation pairs indexed by [m] → relation pairs indexed by a finite type ι; reason: a finite index type is in bijection with [m]
--   - encoding: a constant C → C : ℕ; reason: fixing-set sizes are natural numbers
--   - encoding: F(S), the value on the indicator of S → F applied to SymBoolPCSP.CFixing.indicator S; reason: definition
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §2.1, Theorem 2.2, p.8 (fixing sets and odd parities defined on p.7)

import Mathlib
import Definitions.Def_RobustBoolPCSP_SDP
import Definitions.Def_RobustBoolPCSP_FixingSet

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing in
/-- **Theorem 2.2 (Bounded fixing sets or parity)**, p.8. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Let Γ be a fixed finite Boolean template. Suppose that there is a constant C such that every folded
idempotent polymorphism of Γ, of every arity, either is an odd parity or has a fixing set of size at
most C. Then fiPCSP(Γ) has a perfect integrality gap."

**Formalization Note.** `Γ` is an arbitrary finite Boolean template (not necessarily symmetric, no
`P ⊆ Q`). Folded and idempotent are the published `IsFolded`, `IsIdempotent`; fixing sets have both
halves of the definition of p.7 (`IsFixingSet`), odd parities are `IsOddParity`. Every arity
`L : ℕ` is quantified. -/
theorem theorem_2_2 {ι : Type} [Fintype ι] (Γ : Template ι Bool Bool)
    (hC : ∃ C : ℕ, ∀ (L : ℕ) (F : (Fin L → Bool) → Bool), IsFolded F → IsIdempotent F →
      IsPolB Γ F → IsOddParity F ∨ ∃ J : Finset (Fin L), J.card ≤ C ∧ IsFixingSet F J) :
    HasPerfectGap Γ := by sorry

end RobustBoolPCSP
