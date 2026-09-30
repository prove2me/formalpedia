-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_local_algebra_degree_budget
-- name    : WeierstrassEllipticZeta.stabilizer_local_algebra_degree_budget
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-20T16:11:03.957884+00:00
-- url     : https://prove2.me/theorems/12028a23-76b8-4352-aac4-5f41eb04de2c
-- title:
--   Stabilizer loci with a bounded sum of local algebra lengths
-- statement:
--   Fix a complex period pair with lattice $\Lambda$, its canonical Weierstrass functions, normalized entire sigma differential data, and five entire projective coordinates with no common zero satisfying
--
--   $$
--   S(z)=\sigma(z)^3\bigl(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2\bigr)
--   \qquad(z\notin\Lambda).
--   $$
--
--   Let $\eta:\Lambda\to\mathbb C$ be the integer-linear quasiperiod map. Put
--
--   $$
--   G=\mathbb C\times\bigl(\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\}\bigr),
--   \quad q(v)=(v_0,[(v_1,v_2)]),\quad\phi(z)=(z,[(z,0)]).
--   $$
--
--   There is a constant $C>0$, depending only on these fixed data, with the following property. Let $m,n,U\ge1$, let $X\subset\mathbb C$ be finite with $0\in X$, and let $Q$ be bihomogeneous of bidegree $(m,n)$ in its first two and last five variables. Define
--
--   $$
--   \mathcal F_Q(t,z,u)=Q\bigl(1,t,S_0(z),S_1(z),S_2(z),S_3(z)+uS_0(z),S_4(z)+uS_2(z)\bigr).
--   $$
--
--   Assume $z\mapsto\mathcal F_Q(z,z,0)$ is not identically zero. At each $x\in X+X+X$ and in every available chart $S_j(x)\ne0$, assume the function
--
--   $$
--   z\mapsto Q\bigl(1,z,S_0(z)/S_j(z),\ldots,S_4(z)/S_j(z)\bigr)
--   $$
--
--   has analytic order at least $3U+1$ at $x$.
--
--   Then there are a nonempty locus $W\subseteq\mathbb C^3$ on which $\mathcal F_Q$ vanishes, an integer $0\le b\le2$, and nonnegative integers $e_c$ indexed by $G/H_W$ with the following properties. Here
--
--   $$
--   V_W=\{v:\ w+tv\in W\text{ for every }w\in W,\ t\in\mathbb C\},
--   \quad H_W=q(V_W),\quad Z=\{\phi(x)+H_W:x\in X\}.
--   $$
--
--   For every $c\in Z$, construct a commutative $\mathbb Q$-algebra $R_c$, a prime ideal $\mathfrak p_c$, a derivation $D_c$, an element $q_c\in\mathfrak p_c$ with $D_cq_c\notin\mathfrak p_c$, and an ideal $I_c$ such that
--
--   $$
--   D_c^j f\in\mathfrak p_c\quad(f\in I_c,\ 0\le j\le U),
--   \qquad\operatorname{length}_{R_c}(R_c/I_c)\le e_c.
--   $$
--
--   Their upper bounds must satisfy
--
--   $$
--   \sum_{c\in Z}e_c\le C\,m^{a(W)}n^b,
--   \qquad a(W)=\begin{cases}1&v_0=0\text{ for every }v\in V_W,\\0&\text{otherwise.}\end{cases}
--   $$
--
--   The same $C$ must work for every $X,Q,m,n,U$. Values $e_c$ outside the finite set $Z$ are irrelevant.
--
--   **Formalization Note.** This is a sufficient interface for the remaining geometric construction and degree estimate in [Senthil Kumar (2026), Appendix A, Theorem A.2](https://doi.org/10.1017/S001309152610145X). It separates the algebraic lower bound of [Philippon (1986), Proposition 4.7](https://www.numdam.org/item/10.24033/bsmf.2060.pdf) from the geometric construction and degree comparison in §5, Lemma 5.1. The formal statement does not require the rings to be geometric local rings, but proving it from the paper's argument requires constructing suitable component localizations, verifying derivative containment and transversality, and controlling their total length. None of those existence or upper-bound assertions is assumed to be proved.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Proposition 4.7, pp. 378-379, one transverse direction, and section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. The local derivative-to-length lower bound is proved; selecting geometric component algebras, verifying their derivative hypotheses, and bounding total length remain open.

import Definitions.Def_TranscendenceTheory_DifferentialMultiplicity
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

theorem WeierstrassEllipticZeta.stabilizer_local_algebra_degree_budget
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
          ∃ e : GraphExtensionGroup L.lattice η ⧸ linearTranslationImage L.lattice η W → ℕ,
            (∀ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z)), Nonempty (DifferentialMultiplicityWitness U (e c))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by sorry
