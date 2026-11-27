-- Prove2me | Theorems.Thm_PrivPCP_lemma_4_13_dependent
-- name    : PrivPCP.lemma_4_13_dependent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:52:38.614286+00:00
-- url     : https://prove2.me/theorems/f379db65-b35c-5816-8e9a-4c7154ccd9c8
-- title:
--   Lemma 4.13, dependent case: $\Gamma_F\le ab$
-- statement:
--   This is the multiplicatively dependent case in the proof of Lemma 4.13 in the source.
--
--   Let $q$ be prime, $K=\overline{\mathbb F}_q$, and let $S_1,S_2\le\mathbb F_q^\times$ be subgroups of coprime orders $n_1,n_2$. Let $F\in K[X,Y]$ be irreducible of bidegree $(a,b)$ with $0<a,b<q$, and let $x,y$ be the coordinate functions of its function field. Suppose that $x^{n_1}$ and $y^{n_2}$ are multiplicatively dependent modulo constants, that is, $(x^{n_1})^r(y^{n_2})^s\in K^\times$ for some $(r,s)\ne(0,0)$. Then $\Gamma_F$ is finite and
--
--   $$\Gamma_F\le ab .$$
--
--   In the source, the relation forces $F$ to be a primitive binomial $X^aY^b=\lambda'$ or $X^a=\lambda'Y^b$ with $\gcd(a,b)=1$. Its normalization has a coordinate $z$ with $x=\mu z^b$ and $y=\nu z^{\pm a}$. The common zeros counted by $\Gamma_F$ then solve $z^{bn_1}=c_1$ and $z^{\pm an_2}=c_2$; these roots are simple, and their number is at most $\gcd(bn_1,an_2)=\gcd(b,n_2)\gcd(a,n_1)\le ab$.
--
--   **Formalization Note** The function field and $\Gamma_F$ (`PrivPCP.Supplement.gammaF`) are as in `PrivPCP.Supplement.theorem_4_12`.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), proof of Lemma 4.13, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_PrivPCP_Supplement_gammaF

namespace PrivPCP

theorem lemma_4_13_dependent : ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
    Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
    ∀ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)),
    Irreducible F → 0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F.degreeOf 0 < q → F.degreeOf 1 < q →
    ∀ (L : Type) [Field L] [Algebra (AlgebraicClosure (ZMod q)) L] (x y : L),
    RingHom.ker (MvPolynomial.aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom =
      Ideal.span {F} →
    IntermediateField.adjoin (AlgebraicClosure (ZMod q)) {x, y} = ⊤ →
    (∃ r s : ℤ, ¬ (r = 0 ∧ s = 0) ∧ ∃ c : AlgebraicClosure (ZMod q), c ≠ 0 ∧
      (x ^ Nat.card S₁) ^ r * (y ^ Nat.card S₂) ^ s =
        algebraMap (AlgebraicClosure (ZMod q)) L c) →
    PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂) ≠ ⊤ ∧
    (PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂)).toNat ≤
      F.degreeOf 0 * F.degreeOf 1 := by
  sorry

end PrivPCP
