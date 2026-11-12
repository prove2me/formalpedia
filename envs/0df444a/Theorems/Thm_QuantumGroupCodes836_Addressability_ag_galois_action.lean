-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_ag_galois_action
-- name    : QuantumGroupCodes836.Addressability.ag_galois_action
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:37.295506+00:00
-- url     : https://prove2.me/theorems/f3952a49-7980-4b32-9626-bb0aa1deaec7
-- title:
--   Proposition 2.12 — free Galois action (corrected: nonempty evaluation set)
-- statement:
--   Let $F/B$ be a finite Galois extension of function fields with full finite constants $k$. Let $P$ be a nonempty list of distinct rational places of $F$, unramified over $B$, and let $D$ be disjoint from $P$. Assume the actual Galois group fixes both divisors. Then the evaluation code is a quasi-group code for this same Galois action:
--
--   $$\operatorname{Gal}(F/B)\hookrightarrow\operatorname{PAut}(C_L(P,D)),$$
--
--   with free action on the evaluation coordinates. The coordinate permutation is required to agree with the action on the actual places. The nonempty guard repairs the empty-length exception explained below.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
--   - correction: no nonempty evaluation-set condition in Proposition 2.12 → the evaluation set has positive length; reason: C5: F2(t)/F2(t^2+t), P=0 and D=-P_infinity satisfy the stated invariance and vacuous unramified-place assumptions, but the nontrivial Galois group cannot embed in the permutation group of the empty set
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Proposition 2.12, p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Lifting

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem ag_galois_action {k : Type} [Field k] [Fintype k]
    (B F : FunctionFieldData k) (T : FieldExtension B F)
    (hGalois : letI := T.inclusion.toAlgebra; IsGalois B.carrier F.carrier)
    (P : EvaluationData F) (D : Divisors F) (hpositive : 0 < P.n)
    (hdisjoint : ∀ i, D (P.places i) = 0)
    (hUnramified : ∀ i R, LiesAbove T (P.places i) R → ramificationIndex T (P.places i) R = 1)
    (hInvariant : ∀ σ : extensionAutomorphisms T,
      σ.val • D = D ∧ σ.val • evaluationDivisor P = evaluationDivisor P) :
    ∃ A : CodeAction k (Fin P.n) (extensionAutomorphisms T) (agCode P D),
      ∀ σ j, P.places (A.coordinates σ j) = σ.val • P.places j := by sorry

end QuantumGroupCodes836.Addressability
