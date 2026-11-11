-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_packing_scalar_extension
-- name    : PolynomialPackingMM.IntegerRecursion.packing_scalar_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:59.446924+00:00
-- url     : https://prove2.me/theorems/6e4baee1-5901-4c56-81ca-a9bd1999df24
-- title:
--   §2.2 — scalar extension of exact packing and bilinear identities
-- statement:
--   Exact universal rational coefficient matching has its intended field semantics. For every characteristic-zero field $F$ and arbitrary scalar-entry input lists, an exact PP or SL-PP satisfies
--
--   $$D\bigl(S(E^L A,E^R B)\bigr)=T(A,B).$$
--
--   For exact rank-$r$ bilinear data the corresponding sum of $r$ products of linear forms equals the same target map. This supports reuse over every characteristic-zero field without inferring a universal identity from numerical tests. **Formalization Note** SL sources receive the same common input, and the three clauses use the actual encoders, source products and decoder.
--
--   Differences from the source:
--   - encoding: positive integer parameters and finite coefficient lists → positive naturals, zero-based finite indices and universal ordered coefficient identities; reason: the domains and every coefficient agree, and coefficient matching is valid over every characteristic-zero field
--   - generalization: at least one monomial variable → the empty variable list is also allowed; reason: it is the tensor unit and the same formulas specialize to all source products
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 9 (PDF 10), Definition 2.2, equation (3); rational bilinear algorithms, p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_Packing

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem packing_scalar_extension :
  (∀ (T S : Tasks) (D : PackingData T S), D.Valid .exact →
    ∀ (F : Type) [Field F] [CharZero F]
      (A : LeftIndex T → F) (B : RightIndex T → F),
      (fun o => ∑ c : OutputIndex S, ((D.decode o c).coeff 0 : F) *
        selectedEvaluation S
          (fun x => ∑ a, ((D.left x a).coeff 0 : F) * A a)
          (fun y => ∑ b, ((D.right y b).coeff 0 : F) * B b) c) =
        selectedEvaluation T A B) ∧
  (∀ (T S : Tasks) (D : SLPackingData T S), D.Valid .exact →
    ∀ (F : Type) [Field F] [CharZero F]
      (A : Key → F) (B : RightIndex T → F),
      (fun o => ∑ c : OutputIndex S, ((D.decode o c).coeff 0 : F) *
        selectedEvaluation S (fun x => A x.2.val)
          (fun y => ∑ b, ((D.right y b).coeff 0 : F) * B b) c) =
        selectedEvaluation T (fun a => A a.2.val) B) ∧
  (∀ (T : Tasks) (r : ℕ) (D : BilinearData T r), D.Valid .exact →
    ∀ (F : Type) [Field F] [CharZero F]
      (A : LeftIndex T → F) (B : RightIndex T → F),
      (fun o => ∑ ν : Fin r,
        (∑ a, ((D.left ν a).coeff 0 : F) * A a) *
        (∑ b, ((D.right ν b).coeff 0 : F) * B b) * ((D.weight o ν).coeff 0 : F)) =
        selectedEvaluation T A B) := by sorry

end PolynomialPackingMM.IntegerRecursion
