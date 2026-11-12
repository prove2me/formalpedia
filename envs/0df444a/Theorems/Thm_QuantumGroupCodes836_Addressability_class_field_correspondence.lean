-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_class_field_correspondence
-- name    : QuantumGroupCodes836.Addressability.class_field_correspondence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:09:38.745505+00:00
-- url     : https://prove2.me/theorems/916cfe56-9071-4796-b59d-a8e000932da5
-- title:
--   Theorem 4.3 — class-field correspondence and splitting
-- statement:
--   For a function field $F/k$ with finite full constants and a rational place $P$, there is a class-field isomorphism and a bijection between subgroups $H$ of the actual degree-zero Picard group and unramified abelian intermediate extensions $F_H$ of a fixed separable closure in which $P$ splits:
--
--   $$\operatorname{Gal}(\operatorname{Hil}_P(F)/F)\cong\operatorname{Pic}^0(F),\qquad \operatorname{Gal}(F_H/F)\cong\operatorname{Pic}^0(F)/H.$$
--
--   The quotient isomorphisms commute with restriction of automorphisms. For every rational place $Q$, splitting in $F_H$ is equivalent to $[Q-P]\in H$. This includes both directions of the splitting criterion.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorem 4.3, p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_ClassFields

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem class_field_correspondence {k Ω : Type} [Field k] [Fintype k]
    (F : FunctionFieldData k) [Field Ω] [Algebra F.carrier Ω]
    [IsSepClosed Ω] [Algebra.IsAlgebraic F.carrier Ω] [Algebra.IsSeparable F.carrier Ω]
    (P : Places F) (hP : P.deg = 1) :
    let Hil := hilbertClassField F (Ω := Ω) P
    ∃ artin : (Hil ≃ₐ[F.carrier] Hil) ≃* Multiplicative (AlgebraicCurve.Pic0 k F.carrier),
    ∃ correspondence : AddSubgroup (AlgebraicCurve.Pic0 k F.carrier) ≃
        {K : IntermediateField F.carrier Ω // AdmissibleClassField F P K},
      ∀ H,
      let K := (correspondence H).val
      letI : Algebra k K := ((algebraMap F.carrier K).comp (algebraMap k F.carrier)).toAlgebra
      ∃ quotientIso : (K ≃ₐ[F.carrier] K) ≃* Multiplicative (AlgebraicCurve.Pic0 k F.carrier ⧸ H),
      (∀ σ : Hil ≃ₐ[F.carrier] Hil, ∃ τ : K ≃ₐ[F.carrier] K,
        quotientIso τ = Multiplicative.ofAdd (QuotientAddGroup.mk (Multiplicative.toAdd (artin σ))) ∧
        ∀ x : K, ∃ y : Hil, (x : Ω) = (y : Ω) ∧ (σ y : Ω) = (τ x : Ω)) ∧
      (∀ (Q : Places F) (hQ : Q.deg = 1),
        rawSplits (algebraMap F.carrier K) Q ↔ differenceClass P Q hP hQ ∈ H) := by sorry

end QuantumGroupCodes836.Addressability
