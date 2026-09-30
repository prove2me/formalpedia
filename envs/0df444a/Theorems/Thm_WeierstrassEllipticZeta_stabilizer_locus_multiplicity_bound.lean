-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_locus_multiplicity_bound
-- name    : WeierstrassEllipticZeta.stabilizer_locus_multiplicity_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-20T06:08:34.875902+00:00
-- url     : https://prove2.me/theorems/01b3e331-d405-4501-9bee-ab8e1e525524
-- title:
--   Locus selection with a uniform stabilizer multiplicity bound
-- statement:
--   Fix a complex period pair with lattice $\Lambda$, its canonical Weierstrass functions, normalized entire sigma differential data, and five entire projective coordinates with no common zero:
--
--   $$
--   S(z)=\sigma(z)^3\bigl(1,\wp(z),\wp'(z),\zeta(z),
--   \wp'(z)\zeta(z)+2\wp(z)^2\bigr)\qquad(z\notin\Lambda).
--   $$
--
--   Let $\eta:\Lambda\to\mathbb C$ be the integer-linear quasiperiod map. Write
--
--   $$
--   G=\mathbb C\times\bigl(\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\}\bigr),
--   \quad q(v)=(v_0,[(v_1,v_2)]),\quad\phi(z)=(z,[(z,0)]).
--   $$
--
--   There is a constant $C>0$, depending only on the fixed data, with the following property. Let $m,n,U\ge1$, let $X\subset\mathbb C$ be finite with $0\in X$, and let $Q$ be bihomogeneous of bidegree $(m,n)$ in its first two and last five variables. Put
--
--   $$
--   \mathcal F_Q(t,z,u)=Q\bigl(1,t,S_0(z),S_1(z),S_2(z),
--   S_3(z)+uS_0(z),S_4(z)+uS_2(z)\bigr).
--   $$
--
--   Assume $z\mapsto\mathcal F_Q(z,z,0)$ is not identically zero. At every $x\in X+X+X$ and for every $j$ with $S_j(x)\ne0$, assume the analytic order at $x$ of
--
--   $$
--   z\longmapsto Q\bigl(1,z,S_0(z)/S_j(z),\ldots,S_4(z)/S_j(z)\bigr)
--   $$
--
--   is at least $3U+1$.
--
--   Then there exist a nonempty set $W\subseteq\mathbb C^3$ and an integer $0\le b\le2$ such that $\mathcal F_Q$ vanishes on $W$ and
--
--   $$
--   (U+1)\#\bigl((\phi(X)+H_W)/H_W\bigr)\le C\,m^{a(W)}n^b,
--   $$
--
--   where the subgroup and exponent are fixed by the locus:
--
--   $$
--   V_W=\{v:\ w+tv\in W\text{ for all }t\in\mathbb C,\ w\in W\},
--   \quad H_W=q(V_W),\quad
--   a(W)=\begin{cases}1&v_0=0\text{ for every }v\in V_W,\\0&\text{otherwise.}\end{cases}
--   $$
--
--   The constant is uniform in $X,Q,m,n,U$. The substantive obligation is the choice of $W$ and the displayed degree bound. The construction of the parametrized proper subgroup from a chosen nonempty locus is a separate proved theorem.
--
--   **Formalization Note.** This is a concrete locus-selection formulation of the remaining multiplicity step for [Senthil Kumar (2026), Appendix A, Theorem A.2](https://doi.org/10.1017/S001309152610145X). It follows the stabilizer construction in [Philippon (1986), §5, Lemma 5.1, pp. 380–382](https://www.numdam.org/item/10.24033/bsmf.2060.pdf). The set $W$ may be a lifted algebraic locus, but the formal statement does not require a formal variety structure. It does not assume an identification of $H_W$ with an algebraic stabilizer or assert that the uniform bound has already been proved.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2 and section A.2. https://doi.org/10.1017/S001309152610145X. Specialized covering-space translation-direction construction; no algebraic-stabilizer identification is assumed. Uniform locus selection and its multiplicity bound remain open.

import Definitions.Def_TranscendenceTheory_LinearTranslationStabilizer
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise
open TranscendenceTheory

open scoped Classical

theorem WeierstrassEllipticZeta.stabilizer_locus_multiplicity_bound
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v) →
        ∃ (W : Set (Fin 3 → ℂ)) (b : ℕ), W.Nonempty ∧
          (∀ w ∈ W,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            ((linearTranslationImage L.lattice η W).mkQ ''
              (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
              (n : ℝ) ^ b := by sorry
