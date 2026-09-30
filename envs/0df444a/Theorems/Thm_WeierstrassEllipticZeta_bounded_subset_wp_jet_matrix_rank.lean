-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_wp_jet_matrix_rank
-- name    : WeierstrassEllipticZeta.bounded_subset_wp_jet_matrix_rank
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-14T03:08:47.558061+00:00
-- url     : https://prove2.me/theorems/c86e9b67-82c2-40be-ab98-ad6551efe527
-- title:
--   Quadratic rank bound for the elliptic coordinate jet matrix
-- statement:
--   There is a positive real constant $C$, depending only on the mission geometry $G$, with the following property. Let $m,n\ge1$, let $U$ lie in the specified finite jet range with $U\ge1$, and let $X\subset\mathbb C$ be finite with $0\in X$. Let $Q$ have bidegree $(m,n)$ and satisfy the parent's exact chart hypotheses: a unique nonzero local order below $G.B(m+2n)$ at every regular chart point, order at least $3U+1$ on $X+X+X$, the specified analytic factorization, the bounds on all chart-derivation degrees, and the chart certificates.
--
--   For every $Y\subseteq X$ containing zero and satisfying
--   $$|Y|=\left\lfloor\frac{Cmn^2}{U+1}\right\rfloor_++1,$$
--   let $Z=Y\setminus\Lambda$, $N=3U+1$, and $D=N|Z|$. In chart zero, form the finite matrix
--   $$J_{(z,j),k}=\bigl(\delta_0^j(X_1^k)\bigr)(v_z),\qquad z\in Z,\ 0\le j<N,\ 0\le k<D.$$
--   Then
--   $$2\operatorname{rank}_{\mathbb C}J+(U+1)\le Cn^2.$$
--
--   Coordinate $X_1$ is the elliptic coordinate in this chart. The finite range of $U$, all hypotheses on $Q$, the subset threshold, and the additive $U+1$ term are exactly those of `bounded_subset_wp_cyclic_dimension`. The proved jet-rank identity makes the two bounds equivalent with the same $C$. This quantitative rank estimate remains open.
-- source:
--   Derived linear-algebra construction for https://prove2.me/theorems/0a5b5931-7355-4844-a69c-f0c5659be7aa. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an independent exact rank formula in the already formalized chart contact geometry, not a transcription of the paper zero-estimate proof. Primary Lean sources: Mathlib LinearAlgebra/Isomorphisms.lean, LinearAlgebra/Matrix/Rank.lean, FieldTheory/Minpoly/Finite.lean, and RingTheory/IntegralClosure/IsIntegral/Basic.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The quadratic jet-matrix rank bound remains open and is equivalent to the selected coordinate-dimension frontier with the identical uniform constant.

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem WeierstrassEllipticZeta.bounded_subset_wp_jet_matrix_rank (G : Frontier.Geometry) :
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
            ∀ Y : Finset ℂ, Y ⊆ X → 0 ∈ Y →
              Y.card = ⌊(C * (m : ℝ) * (n : ℝ) ^ 2) /
                (((U : ℕ) + 1 : ℕ) : ℝ)⌋₊ + 1 →
              let Z := Y.filter (fun z => z ∉ G.L.lattice)
              let N := 3 * (U : ℕ) + 1
              let J : Matrix (Z × Fin N) (Fin (N * Z.card)) ℂ := Matrix.of fun r k =>
                MvPolynomial.eval (extensionChartCoordinates G.S 0 r.1.val)
                  ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[r.2.val]
                    (MvPolynomial.X (1 : Fin 4) ^ k.val))
              ((2 * J.rank + ((U : ℕ) + 1) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ 2 := by sorry
