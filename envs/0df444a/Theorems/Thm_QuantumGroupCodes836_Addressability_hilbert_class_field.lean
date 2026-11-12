-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_hilbert_class_field
-- name    : QuantumGroupCodes836.Addressability.hilbert_class_field
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:09:33.562989+00:00
-- url     : https://prove2.me/theorems/0f01e7d1-cf23-4f63-8893-44a58f954ddd
-- title:
--   Proposition 4.2 — Hilbert class-field existence and constants
-- statement:
--   Let $F/k$ be a one-variable function field with full finite constants $k$, let $P$ be rational, and fix a separable closure. The supremum defining the Hilbert class field is itself a finite unramified abelian extension in which $P$ splits, and contains every such extension. It also contains every algebraic extension whose finite subextensions have these properties. Its full constant field is unchanged:
--
--   $$\operatorname{Const}(\operatorname{Hil}_P(F))=k.$$
--
--   This is existence and maximality, rather than an assumption that a suitable extension has already been supplied.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
--   - reading: maximum unramified abelian extension of F in F_sep in which P splits completely → the supremum K of the finite such extensions is itself one, and every intermediate field all of whose finite subextensions are such extensions lies in K; reason: an infinite algebraic extension is unramified abelian with P split exactly when its finite subextensions are
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Proposition 4.2, p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_ClassFields

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem hilbert_class_field {k Ω : Type} [Field k] [Fintype k]
    (F : FunctionFieldData k) [Field Ω] [Algebra F.carrier Ω]
    [IsSepClosed Ω] [Algebra.IsAlgebraic F.carrier Ω] [Algebra.IsSeparable F.carrier Ω]
    (P : Places F) (hP : P.deg = 1) :
    let K := hilbertClassField F (Ω := Ω) P
    letI : Algebra k K := ((algebraMap F.carrier K).comp (algebraMap k F.carrier)).toAlgebra
    AdmissibleClassField F P K ∧
    (∀ J, AdmissibleClassField F P J → J ≤ K) ∧
    (∀ J : IntermediateField F.carrier Ω,
      (∀ I : IntermediateField F.carrier Ω, I ≤ J → Module.Finite F.carrier I →
        AdmissibleClassField F P I) → J ≤ K) ∧
    (∀ x : K, IsAlgebraic k x → ∃ a : k, algebraMap k K a = x) := by sorry

end QuantumGroupCodes836.Addressability
