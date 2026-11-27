-- Prove2me | Theorems.Thm_PrivPCP_lemma_4_13_gamma_upper
-- name    : PrivPCP.lemma_4_13_gamma_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T03:48:53.275927+00:00
-- url     : https://prove2.me/theorems/933ad575-c676-5569-86fc-cf0f95900a4e
-- title:
--   Lemma 4.13, upper bound $\Gamma_F\le C(N^{1/3}(ab)^{2/3}+ab)$
-- statement:
--   This is the combined upper bound on $\Gamma_F$ in the proof of Lemma 4.13 in the source. It covers both the multiplicatively independent case (Theorem 4.12, Corvaja–Zannier) and the dependent (binomial) case.
--
--   There is an absolute constant $C$ such that the following holds. Let $q$ be prime, $K=\overline{\mathbb F}_q$, and let $S_1,S_2\le\mathbb F_q^\times$ be subgroups of coprime orders $n_1,n_2$, with $N=n_1n_2$. Let $F\in K[X,Y]$ be irreducible of bidegree $(a,b)$ with $0<a,b<q$, and let $x,y$ be the coordinate functions of its function field. Then $\Gamma_F$ is finite and
--
--   $$\Gamma_F\ \le\ C\big(N^{1/3}(ab)^{2/3}+ab\big).$$
--
--   In the source, $N\mid q-1$ gives $N<q$, and $a,b<q$ give $dx,dy\ne0$. If $x^{n_1}$ and $y^{n_2}$ are multiplicatively independent modulo constants, Theorem 4.12 applies. Otherwise $F$ is a primitive binomial, and a direct parametrization gives $\Gamma_F\le\gcd(bn_1,an_2)\le ab$.
--
--   **Formalization Note** The function field and $\Gamma_F$ (`PrivPCP.Supplement.gammaF`) are as in `PrivPCP.Supplement.theorem_4_12`. The constant $C$ is fixed before $q$, $F$, $S_1$ and $S_2$.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), §4.4.1 pp.22-23 and proof of Lemma 4.13, pp.24-25 (PDF pp.26-27); Theorem 4.12, p.23

import Mathlib
import Definitions.Def_PrivPCP_Supplement_gammaF

namespace PrivPCP

theorem lemma_4_13_gamma_upper : ∃ C : ℝ, ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
    Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
    ∀ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)),
    Irreducible F → 0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F.degreeOf 0 < q → F.degreeOf 1 < q →
    ∀ (L : Type) [Field L] [Algebra (AlgebraicClosure (ZMod q)) L] (x y : L),
    RingHom.ker (MvPolynomial.aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom =
      Ideal.span {F} →
    IntermediateField.adjoin (AlgebraicClosure (ZMod q)) {x, y} = ⊤ →
    PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂) ≠ ⊤ ∧
    ((PrivPCP.Supplement.gammaF (AlgebraicClosure (ZMod q)) L x y (Nat.card S₁) (Nat.card S₂)).toNat : ℝ) ≤
      C * (((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
          ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) +
        ((F.degreeOf 0 * F.degreeOf 1 : ℕ) : ℝ)) := by
  sorry

end PrivPCP
