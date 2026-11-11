-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_5_9
-- name    : ShortestPlanarDisjoint.Main.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:56.360099+00:00
-- url     : https://prove2.me/theorems/47541566-918e-4074-9413-f999a87d8520
-- title:
--   Lemma 5.9 — Terminal basis, cap insertion and conversion cost
-- statement:
--   All three parts concern a block of h positions. (a) The polynomials B_sigma are a basis of the multiaffine polynomials. Their leading monomials are the products of t_i at x positions, with coefficient one, and the change-of-basis matrix is unit triangular. (b) For every admissible cap set C and core word rho, cap insertion is injective, C(C star rho)=C union C(rho), and B_{C star rho}=Delta_C B_rho after order-preserving relabelling. Multiplication of any core polynomial by Delta_C preserves its inserted coefficients. Every nonzero resulting coordinate is inserted from a nonzero core coordinate and its cap set contains C. (c) There is one absolute A such that for every h an actual addition program converts every ordinary coefficient array in at most A(h+1)^2 2^h additions.
--
--   Differences from the source:
--   - generalization: coefficients in the characteristic-two polynomial/Laurent algebra of the other variables → every commutative characteristic-two coefficient ring, with a conversion program and count uniform over rings; reason: the source's coefficient algebras are included; the identities use only commutative characteristic-two arithmetic and no division
--   - encoding: ordered positions, caps, core relabelling and arithmetic additions → zero-based Fin h, Boolean words with true=x and false=y, increasing finite cap pairs, the order embedding of uncovered positions and addition-only register programs; reason: all clauses, coefficient consequences and the exact uniform O((h+1)^2 2^h) operation count are retained; h=0 is the constant basis
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 5.9, p. 27 (PDF p. 29)

import Definitions.Def_ShortestPlanarDisjoint_Main_TerminalBasis
set_option autoImplicit false
universe u

namespace ShortestPlanarDisjoint.Main
/-- All three parts of Lemma 5.9, including the coefficient/support consequence of
cap insertion and a uniform addition-count bound for actual conversion programs. -/
theorem lemma_5_9 :
    (∀ (R : Type u) [CommRing R] [CharP R 2] (h : ℕ),
      (∀ word : BlockWord h, IsMultiaffine (blockBasis (R := R) word) ∧
        (blockBasis (R := R) word).coeff (wordExponent word) = 1 ∧
        ∀ a ∈ (blockBasis (R := R) word).support,
          ¬ ExponentLexLT (List.finRange h)
            (fun i => (wordExponent word i : ℤ)) (fun i => (a i : ℤ))) ∧
      LinearIndependent R (@blockBasis R _ h) ∧
      (∀ p : BlockPolynomial R h, IsMultiaffine p →
        ∃! c : BlockWord h → R, basisPolynomial c = p) ∧
      (∀ word other : BlockWord h,
        ExponentLexLT (List.finRange h)
          (fun i => (wordExponent other i : ℤ)) (fun i => (wordExponent word i : ℤ)) →
        (blockBasis (R := R) other).coeff (wordExponent word) = 0)) ∧
    (∀ (R : Type u) [CommRing R] [CharP R 2] (h : ℕ) (C : AdmissibleCaps h),
      Function.Injective C.insertWord ∧
      (∀ word : BlockWord C.free.card,
        blockCaps (C.insertWord word) = C.pairs ∪ C.liftCaps word ∧
        blockBasis (R := R) (C.insertWord word) =
          C.delta * MvPolynomial.rename C.freePosition (blockBasis (R := R) word)) ∧
      (∀ c : BlockWord C.free.card → R,
        C.delta * MvPolynomial.rename C.freePosition (basisPolynomial c) =
          ∑ word : BlockWord C.free.card,
            MvPolynomial.C (c word) * blockBasis (R := R) (C.insertWord word)) ∧
      (∀ (c : BlockWord C.free.card → R) (d : BlockWord h → R),
        basisPolynomial d = C.delta * MvPolynomial.rename C.freePosition (basisPolynomial c) →
        (∀ word, d (C.insertWord word) = c word) ∧
        (∀ word, d word ≠ 0 → ∃ core, c core ≠ 0 ∧ C.insertWord core = word ∧
          C.pairs ⊆ blockCaps word))) ∧
    (∃ A : ℕ, 0 < A ∧ ∀ h : ℕ, ∃ P : AdditionProgram h,
      P.additions.length ≤ A * (h + 1) ^ 2 * 2 ^ h ∧
      ∀ (R : Type u) [CommRing R] [CharP R 2] (input : BlockWord h → R), basisPolynomial (P.eval input) = ordinaryPolynomial input) := by sorry
end ShortestPlanarDisjoint.Main
