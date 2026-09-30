-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_isolated_component_degree_budget
-- name    : WeierstrassEllipticZeta.stabilizer_isolated_component_degree_budget
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-20T17:32:18.967843+00:00
-- url     : https://prove2.me/theorems/025a7b58-a701-461a-86f4-e1e08080993b
-- title:
--   Stabilizer loci with isolated component degree data
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
--   For every $c\in Z$, construct a commutative $\mathbb Q$-algebra $R_c$, a prime ideal $\mathfrak p_c$, a derivation $D_c$, and an element $q_c\in\mathfrak p_c$ with $D_cq_c\notin\mathfrak p_c$. Also construct a finite family of ideals $J_{c,0},\ldots,J_{c,r_c-1}$ and a distinguished index $i_c<r_c$ such that
--
--   $$
--   J_{c,j}\not\subseteq\mathfrak p_c\qquad(j\ne i_c).
--   $$
--
--   Put $I_c=\bigcap_{j<r_c}J_{c,j}$ and $S_c=(R_c)_{\mathfrak p_c}$. The required derivative and length conditions are
--
--   $$
--   D_c^k f\in\mathfrak p_c\quad(f\in I_c,\ 0\le k\le U),
--   \qquad\operatorname{length}_{S_c}(S_c/I_cS_c)\le e_c.
--   $$
--
--   Here $I_cS_c$ denotes extension under the canonical localization map. Derivative containment is required only for the full intersection, and no primaryness hypothesis is imposed on the family. The separate component-isolation theorem transfers these conditions to the selected component.
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
--   **Formalization Note.** This is the remaining construction and degree estimate needed for [Senthil Kumar (2026), Appendix A, Theorem A.2](https://doi.org/10.1017/S001309152610145X). The component-isolation step is formalized separately from [Philippon (1986), Proposition 4.7, p. 379](https://www.numdam.org/item/10.24033/bsmf.2060.pdf). The formal statement does not impose an identification of its rings or ideals with geometric components. Constructing suitable data from that geometry, including separation, transversality, derivative containment, and the total degree budget, remains open. A singleton family recovers the previous prime-data formulation, so this interface does not impose a stronger requirement.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Proposition 4.7, especially p. 379, and section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Algebraic auxiliary theorem: isolate an ideal component with a separator outside the prime and prove preservation of the local quotient and finite-order derivative containment. Component selection, global transversality, and the total local-length degree budget remain open.

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

theorem WeierstrassEllipticZeta.stabilizer_isolated_component_degree_budget
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
              (extensionCurve L.lattice η z)), Nonempty (IsolatedComponentMultiplicityData U (e c))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by sorry
