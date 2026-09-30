-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_canonical_orbit_base_degree_budget
-- name    : WeierstrassEllipticZeta.stabilizer_canonical_orbit_base_degree_budget
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-20T20:35:28.798308+00:00
-- url     : https://prove2.me/theorems/68be6473-e667-4776-9a12-c7087f185295
-- title:
--   Stabilizer degree budget for canonical analytic-orbit base ideals
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
--   For every $c\in Z$, choose a chart index $j_c\in\{0,1\}$ and a point $z_c\in X+X+X$ in that chart. The denominators are $S_0$ for chart zero and $S_2$ for chart one; the chosen denominator at $z_c$ must be nonzero.
--
--   Use the fixed ring $A=\mathbb C[T,X_1,X_2,X_3]$. In chart zero write its coordinates $(t,x,y,u)$ and in chart one $(t,a,b,h)$. Define the normalized polynomials
--
--   $$Q_0(t,x,y,u)=Q(1,t,1,x,y,u,yu+2x^2),\qquad
--   Q_1(t,a,b,h)=Q(1,t,a,b,1,ah-2b^2,h).$$
--
--   The corresponding orbit coordinates are
--
--   $$v_0(z)=(z,S_1/S_0,S_2/S_0,S_3/S_0),\qquad
--   v_1(z)=(z,S_0/S_2,S_1/S_2,S_4/S_2).$$
--
--   The fixed complex derivations are determined on the variables by
--
--   $$\delta_0(t,x,y,u)=(1,y,6x^2-g_2/2,-x),$$
--   $$\delta_1(t,a,b,h)=(1,-6b^2+(g_2/2)a^2,
--   -1/2-g_2ab-(3g_3/2)a^2,-2g_2b^2-3g_3ab).$$
--
--   For the derivation $\delta_{j_c}$ define, for any ideal $J\subseteq A$,
--
--   $$P_r(J)=\bigl(\delta_{j_c}^k f:f\in J,\ 0\le k\le r\bigr).$$
--
--   The base ideal is now fixed by the chart and point:
--
--   $$K_c=\{r\in A:r(v_{j_c}(w))=0\text{ for all }w\text{ near }z_c\},\qquad
--   J_c=K_c+(Q_{j_c}).$$
--
--   Put
--
--   $$\mathfrak q_c=\ker\bigl(A\xrightarrow{\operatorname{eval}_{v_{j_c}(z_c)}}\mathbb C\bigr).$$
--
--   For **every** $i\in\{0,1,2\}$ and every prime $\mathfrak p\subseteq\mathfrak q_c$ that is minimal over both $P_{iU}(J_c)$ and $P_{(i+1)U}(J_c)$, require
--
--   $$\operatorname{length}_{A_{\mathfrak p}}\bigl(A_{\mathfrak p}/P_{iU}(J_c)A_{\mathfrak p}\bigr)\le e_c.$$
--
--   The complete canonical-base theorem proves from the stated analytic hypotheses that $J_c$ has height at least two, contains $Q_{j_c}$, and satisfies $P_{3U}(J_c)\subseteq\mathfrak q_c$. These are no longer witness fields. The previously proved selection criterion then gives a qualifying common minimal prime at an adjacent pair with starting stage in $\{0,U,2U\}$.
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
--   **Formalization Note.** This is the remaining locus and degree-budget statement for the canonical analytic-orbit base ideals, in the zero-estimate framework of [Senthil Kumar (2026), Appendix A, Theorem A.2](https://doi.org/10.1017/S001309152610145X). The starting-ideal pattern is from [Philippon (1986), §5, p. 380](https://www.numdam.org/item/10.24033/bsmf.2060.pdf). Here the relation ideal is defined as the local analytic-orbit kernel; its equality with the full algebraic-group ideal is not asserted. The current theorem remains Open and must produce the locus, available chart points in the triple sumset, and the uniform total degree budget for these fixed ideals. No converse for arbitrary previous base ideals is claimed. The constant, degree exponents and numerical sum inequality are unchanged.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, p. 380: starting ideal obtained by adjoining the polynomial equation to an ambient relation ideal, and derivative ideals contained in evaluation ideals at points of high vanishing. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. The complete theorem constructs the canonical base from the local analytic-orbit kernel and the normalized polynomial, and proves height at least two, membership and terminal derivative containment in both Weierstrass charts. Identification of this germ kernel with the entire algebraic-group ideal is not asserted. The remaining child must select the locus and chart points and prove a uniform total-length degree budget for this specific base ideal; no converse for arbitrary previous bases is claimed.

import Definitions.Def_WeierstrassEllipticZeta_ChartOrbitBase
import Definitions.Def_WeierstrassEllipticZeta_ChartSelectionData
import Definitions.Def_WeierstrassEllipticZeta_ChartProlongationData
import Definitions.Def_WeierstrassEllipticZeta_ChartPrimeMultiplicityData
import Definitions.Def_TranscendenceTheory_AnalyticOrbitMultiplicityData
import Definitions.Def_TranscendenceTheory_MinimalPrimeMultiplicityData
import Definitions.Def_TranscendenceTheory_IsolatedComponentMultiplicityData
import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData
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

theorem WeierstrassEllipticZeta.stabilizer_canonical_orbit_base_degree_budget
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
              (extensionCurve L.lattice η z)), Nonempty (ChartOrbitBaseBudget L S Q U (e c) (X + X + X))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by sorry
