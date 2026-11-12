-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_ag_multiplication
-- name    : QuantumGroupCodes836.Addressability.ag_multiplication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:28.111383+00:00
-- url     : https://prove2.me/theorems/10d177a2-4b8a-4955-a0e9-1448c0aecab1
-- title:
--   Proposition 2.13 — all-one word and multiplication criterion
-- statement:
--   Let $F/k$ have full finite constants, let $P$ sum distinct rational places, and let $D$ be effective and disjoint from $P$. Then the actual evaluation code contains the all-one word. For every positive integer $m$ and differential $\eta$ with simple poles at $P$, if $(m+1)D\le P+(\eta)$, its nonzero residue weights satisfy
--
--   $$u\star C_L(P,D)^{\star m}\subseteq C_L(P,D)^\perp,\qquad u_i=\operatorname{Res}_{P_i}(\eta).$$
--
--   This supplies both the all-one word and the weighted multiplication property used later.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
--   - encoding: a differential with divisor and simple poles → a nonzero Kähler differential; reason: the zero differential has no divisor or simple pole; no defined source instance is excluded
--   - encoding: let m be an integer → 1 ≤ m; reason: Definition 2.7 defines the m-multiplication property only for m ≥ 1
--   - generalization: C_L(P,D) satisfies the m-multiplication property (some nonzero weight vector) → the weight vector is the residue vector (Res_{P_i}(η))_i; reason: this is the vector of the proof on p.8; the Lean conclusion implies the source one
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Proposition 2.13, p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Lifting

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem ag_multiplication {k : Type} [Field k] [Fintype k] (F : FunctionFieldData k)
    (P : EvaluationData F) (D : Divisors F)
    (hdisjoint : ∀ i, D (P.places i) = 0) (hD : effective D) :
    (1 : Fin P.n → k) ∈ agCode P D ∧
    ∀ m : ℕ, 1 ≤ m → ∀ η : KaehlerDifferential k F.carrier,
      η ≠ 0 → (∀ i, (P.places i).ordDifferential η = -1) →
      (m + 1) • D ≤ evaluationDivisor P + differentialDivisor η →
      MultiplicationWith (agCode P D) m (fun i => simplePoleResidue (P.places i) η) := by sorry

end QuantumGroupCodes836.Addressability
