-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_63
-- name    : SingleInteraction.Supplement.theorem_63
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:09:17.279614+00:00
-- url     : https://prove2.me/theorems/bd1a703c-2438-4b59-ac37-8fc3a74d5c99
-- title:
--   Theorem 63 — SIH$_2$ with $h_{\alpha,\beta}$: QMA-complete ($\alpha>0,\beta\ne0$), NP-complete ($\alpha>0,\beta=0$), in P ($\alpha<0,|\beta|\le|\alpha|$, or $\alpha=\beta=0$)
-- statement:
--   Let $\alpha,\beta$ be fixed real constants for which $h_{\alpha,\beta}=\alpha\,Z\otimes Z+\beta(X\otimes Y-Y\otimes X)$ (eq. (40)) has polynomial-time computable entries. The problem SIH$_2$ with interaction $h_{\alpha,\beta}$ is
--
--   1. QMA-complete if $\alpha>0$ and $\beta\ne0$;
--   2. NP-complete if $\alpha>0$ and $\beta=0$;
--   3. in P if $\alpha<0$ and $|\beta|\le|\alpha|$, or if $\alpha=\beta=0$.
--
--   This is a partial classification of the two-parameter family: on the ray $\alpha>0$ the problem jumps from NP-complete at $\beta=0$ to QMA-complete at every $\beta\ne0$.
--
--   Differences from the source:
--   - reading: α, β ∈ ℝ fixed, efficiently computable constants (p.67) → arbitrary reals α, β with EntriesPolyTime (h_{α,β}); reason: that is the computability Definition 31 asks of the interaction
--   - encoding: X-complete, with poly(n) bit lengths and an inverse-polynomial gap → membership for every exponent c and X-hardness for some c of the problem at exponent c; reason: the published theorem_60 convention; hardness at c implies hardness at every c′ ≥ c because the valid sets grow
--   - reading: QMA (Definition 2, p.16; an adapted, equivalent form by Remark 1) → the published InQMA / QMAHard: uniform polynomial-size {H, T, CNOT} verifiers, completeness 2/3, soundness 1/3, polynomial-time many-one reductions; reason: the base mission’s declared reading of Definition 2 (Remark 1 calls it equivalent to the standard class)
--   - encoding: NP, P (eq. (1)) → InNP / NPHard / InP of Def_SingleInteraction_Supplement_Classes on the bit-string layer of InQMA; reason: the standard classes for promise problems
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 63, p.67

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_sihProblem
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Classes
import Definitions.Def_SingleInteraction_Supplement_Interactions

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 63 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held
version, sha256 19ddc444…), §5.2, p.67): "For the family of interactions `hα,β` defined in eq. (40),
the corresponding `SIH2` problem is: 1. QMA-complete if `α > 0` and `β ≠ 0`; 2. NP-complete if
`α > 0` and `β = 0`; 3. in P if `α < 0` and `|β| ≤ |α|`, or if `α = β = 0`."

For fixed reals `α, β` for which `h_{α,β} = α Z⊗Z + β(X⊗Y − Y⊗X)` has polynomial-time computable
entries (the paper's "fixed, efficiently computable constants", p.67):
1. if `α > 0` and `β ≠ 0`, `SIH_2` with `h_{α,β}` is in QMA for every exponent `c` and QMA-hard for
   some `c`;
2. if `α > 0` and `β = 0`, it is in NP for every `c` and NP-hard for some `c`;
3. if `α < 0` and `|β| ≤ |α|`, or `α = β = 0`, it is in P for every `c`.

**Formalization Note** QMA notions are the published `InQMA` / `QMAHard`; P and NP are those of
`Def_SingleInteraction_Supplement_Classes`, on the same bit-string layer, applied through the base
codec `sihCodec`. "`poly(n)`" is the exponent `c` (membership for every `c`, hardness for some `c`),
as in the published `theorem_60`. -/
theorem theorem_63 (α β : ℝ) (hcomp : EntriesPolyTime (hAB α β)) :
    (0 < α → β ≠ 0 →
      (∀ c : ℕ, InQMA (onCodes sihCodec (sihProblem 2 (hAB α β) c))) ∧
        ∃ c : ℕ, QMAHard sihCodec.encode (sihProblem 2 (hAB α β) c)) ∧
    (0 < α → β = 0 →
      (∀ c : ℕ, InNP (onCodes sihCodec (sihProblem 2 (hAB α β) c))) ∧
        ∃ c : ℕ, NPHard sihCodec.encode (sihProblem 2 (hAB α β) c)) ∧
    ((α < 0 ∧ |β| ≤ |α|) ∨ (α = 0 ∧ β = 0) →
      ∀ c : ℕ, InP (onCodes sihCodec (sihProblem 2 (hAB α β) c))) := by sorry

end Supplement

end SingleInteraction
