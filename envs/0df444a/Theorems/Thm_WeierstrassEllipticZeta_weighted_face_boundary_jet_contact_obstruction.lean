-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_weighted_face_boundary_jet_contact_obstruction
-- name    : WeierstrassEllipticZeta.weighted_face_boundary_jet_contact_obstruction
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-13T04:46:39.818342+00:00
-- url     : https://prove2.me/theorems/1cce73f4-b850-4bca-a245-16357d88ad77
-- title:
--   Degree-weighted face bounds and boundary jet stability at contacts
-- statement:
--   Under the geometric, analytic, degree, and chart-certificate hypotheses of the [box-degree frontier](https://prove2.me/theorems/b747c74b-ad76-48cd-90e9-6075fc3b0c81), there is a positive real constant $C$, independent of the admissible $m,n,U,X,Q$, such that one of the following alternatives holds.
--
--   First, assign every point of $X$ to a valid chart $c\in\{0,1\}$. For each chart choose a coordinate bound $b_c\in\mathbb N^4$ and a nonzero polynomial $p_c$ satisfying $\deg_i p_c\le b_{c,i}$. The polynomial $p_c$ belongs to the contact ideal of order $U+1$ at every assigned point. For the box $S_c=\{d:d_i\le b_{c,i}\}$ and its coordinate boundary
--   $$B_c=\left(\bigcup_{i=0}^3(S_c+e_i)\right)\setminus S_c,$$
--   the joint derivative-evaluation vectors of monomials indexed by $S_c\cup B_c$ span a space of the same dimension as those indexed by $S_c$. The joint vector records the chart derivation iterates of orders $0,\ldots,U$ at all points assigned to that chart. In addition, the degree-weighted coordinate faces satisfy
--   $$\sum_{c=0}^1\sum_{i=0}^3
--    (\deg_i p_c)\prod_{\substack{0\le j\le3\\j\ne i}}(b_{c,j}+1)
--    \le Cmn^2.$$
--
--   Alternatively, if $\pi_\Lambda(X)$ is the set of lattice classes represented by $X$, then
--   $$(U+1)|\pi_\Lambda(X)|\le Cn^2.$$
--
--   This is an open sufficient criterion for the preceding frontier. Bounding these face counts implies the required box-volume difference bound; the converse is not asserted. The contact conditions, boundary ranks, admissibility hypotheses, and uniformity of $C$ are retained.
-- source:
--   Derived box-volume face estimate for the frontier https://prove2.me/theorems/b747c74b-ad76-48cd-90e9-6075fc3b0c81. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting finite-product estimate is proved by induction on the coordinate set using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Algebra/BigOperators/Ring/Finset.lean (mul_sum), Algebra/BigOperators/Group/Finset/Basic.lean (prod_insert and sum_insert), and Data/Finset/Basic.lean (erase_insert and erase_insert_of_ne). The remaining child asks for a sufficient bound on degree-weighted coordinate faces. Constructing suitable contact boxes and the uniform geometric estimate remain open.

import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.weighted_face_boundary_jet_contact_obstruction (G : Frontier.Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, ∀ U : Fin ((G.B (m + 2 * n) - 2) / 3 + 1),
          1 ≤ m → 1 ≤ n → 1 ≤ (U : ℕ) → ∀ X : Finset ℂ,
          0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
            (∀ d ∈ Q.support, d 0 + d 1 = m ∧
              d 2 + d 3 + d 4 + d 5 + d 6 = n) →
            (∀ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 →
              let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
                (extensionChartNormalize c Q)
              ∃! k : ℕ, k < G.B (m + 2 * n) ∧
                (z ∈ X + X + X → 3 * (U : ℕ) + 1 ≤ k) ∧
                (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
                ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
                  f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w)) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n (U : ℕ) X Q →
            ((∃ a : X → Fin 2,
              (∀ x : X, G.S (extensionChartDenominator (a x)) x.val ≠ 0) ∧
              ∃ b : Fin 2 → (Fin 4 →₀ ℕ),
              let S := fun c : Fin 2 => Finset.Iic (b c)
              let B := fun c : Fin 2 => (Finset.univ.biUnion fun i : Fin 4 =>
                (S c).image (fun d => d + Finsupp.single i 1)) \ S c
              let jets := fun (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ)
                (x : {z : X // a z = c}) (k : Fin ((U : ℕ) + 1)) =>
                  MvPolynomial.eval (extensionChartCoordinates G.S c x.val.val)
                    ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val] p)
              ∃ p : Fin 2 → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, ∑ i : Fin 4,
                (p c).degreeOf i * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
                  (b c j + 1) : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, p c ≠ 0) ∧
              (∀ (c : Fin 2) (i : Fin 4), (p c).degreeOf i ≤ b c i) ∧
              (∀ c : Fin 2, ∀ x : {z : X // a z = c},
                p c ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1)) ∧
              ∀ c : Fin 2,
                Module.finrank ℂ (Submodule.span ℂ
                  ((fun d : Fin 4 →₀ ℕ => jets c (MvPolynomial.monomial d 1)) ''
                    ((S c ∪ B c : Finset (Fin 4 →₀ ℕ)) : Set (Fin 4 →₀ ℕ)))) =
                Module.finrank ℂ (Submodule.span ℂ
                  ((fun d : Fin 4 →₀ ℕ => jets c (MvPolynomial.monomial d 1)) ''
                    (S c : Set (Fin 4 →₀ ℕ))))) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by sorry
