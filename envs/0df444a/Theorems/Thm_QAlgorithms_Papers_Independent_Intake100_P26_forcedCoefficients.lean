-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P26_forcedCoefficients
-- name    : QAlgorithms.Papers.Independent.Intake100.P26.forcedCoefficients
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:25:05.323005+00:00
-- url     : https://prove2.me/theorems/0baef2bf-6f16-4376-89ea-15eb24ae8973
-- title:
--   Forced coefficients in a calibrated weight basis
-- statement:
--   Let $R$ be a finite reduced irreducible crystallographic root system of positive rank, with a fixed positive system and simple roots $\alpha_i$, Weyl group $W$, and full weight lattice $P$. Fix $q\in\mathbb C^\times$ which is not a root of unity. Write $\widetilde H$ for its affine Hecke algebra with $T_i^2=(q-q^{-1})T_i+1$ and the Bernstein relation with denominator $1-X^{-\alpha_i}$ interpreted as a Laurent-polynomial divided difference. Let $T=\operatorname{Hom}(P,\mathbb C^\times)$, with $(wt)(X^\lambda)=t(X^{w^{-1}\lambda})$. All modules below are finite dimensional complex left modules. Irreducible modules are nonzero.
--
--   Let $M$ be calibrated. Suppose every occurring weight $b$ satisfies $b(X^{\alpha_i})\ne1$ for every simple root, and $\dim M_b=1$. For each occurring $b$ choose any nonzero vector $v_b\in M_b$. These vectors form a basis, and $X^\lambda v_b=b(X^\lambda)v_b$.
--
--   Write $a_i(c,b)$ for the coefficient of $v_c$ in $T_iv_b$, extending it by zero when a weight is absent, and put $d_i(b)=(q-q^{-1})/(1-b(X^{-\alpha_i}))$. For every occurring $b$,
--   $$a_i(b,b)=d_i(b),\qquad c\ne b,\ a_i(c,b)\ne0\ \Longrightarrow\ c=s_i b,$$
--   $$a_i(b,s_i b)a_i(s_i b,b)=(q^{-1}+d_i(b))(q^{-1}+d_i(s_i b)).$$
--   These identities constrain the generator action for any choices of nonzero weight vectors. The off-diagonal qualification in the second identity repairs the printed omission. If $s_i b$ is absent, the left side is zero and the diagonal scalar on the right is still evaluated by its explicit formula.
-- source:
--   Calibrated representations of affine Hecke algebras, arXiv:math/0401323v2, PDF p. 15, Proposition 4.1(a)–(c)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P26

open scoped BigOperators

variable {D : Datum} {V U : Type*}

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- Proposition 4.1(a)--(c), PDF pp.15--16. The missing off-diagonal condition
in printed (b) is restored from the coefficient comparison in its proof.
When s_i b is absent, off-diagonal entries are zero and its diagonal scalar
is evaluated explicitly, without inventing a basis vector. -/
theorem forcedCoefficients (D : Datum) (q : ℂ) (hq : GoodParameter q)
    (A : HeckeGenerators D V) [FiniteDimensional ℂ V] (hA : Relations q A)
    (hcal : Calibrated A)
    (hregular : ∀ t ∈ weightSupport A, ∀ i, torusCharacterEval t (simpleRootWeight D i) ≠ 1)
    (hmult : ∀ t ∈ weightSupport A, Module.finrank ℂ (weightSpace A t) = 1)
    (v : weightSupport A → V)
    (hv : ∀ t, v t ∈ weightSpace A t.val ∧ v t ≠ 0) :
    ∃ b : Module.Basis (weightSupport A) ℂ V,
      (∀ t, b t = v t) ∧
      (∀ t x, A.X x (b t) = torusCharacterEval t.val x • b t) ∧
      (∀ i t, t ∈ weightSupport A → weightMatrixEntry A b i t t = seminormalDiagonal q t i) ∧
      (∀ i c t, c ≠ t → weightMatrixEntry A b i c t ≠ 0 → c = weylCharacter D (simple D i) t) ∧
      (∀ i t, t ∈ weightSupport A →
        weightMatrixEntry A b i t (weylCharacter D (simple D i) t) *
          weightMatrixEntry A b i (weylCharacter D (simple D i) t) t =
        (q⁻¹ + seminormalDiagonal q t i) * (q⁻¹ + seminormalDiagonal q (weylCharacter D (simple D i) t) i)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P26

end
