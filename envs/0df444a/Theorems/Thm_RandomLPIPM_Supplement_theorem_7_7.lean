-- Prove2me | Theorems.Thm_RandomLPIPM_Supplement_theorem_7_7
-- name    : RandomLPIPM.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:53:22.655206+00:00
-- url     : https://prove2.me/theorems/07321d92-3113-4570-a08d-b38ebaf7acca
-- title:
--   Theorem 7.7 — conditional law of the kernel given the central point
-- statement:
--   Let $A\in\mathbb R^{d\times n}$ have independent $N(0,1)$ entries, $1\le d\le n-1$, and $k=n-d$, the dimension of $\ker A$. Fix $0<\mu<1$. Let $x_\mu(A)$ be the $\mu$-central point of the LP $\min\mathbf 1^\top x$ subject to $Ax=A\mathbf 1$, $x\ge0$; it depends on $A$ only through $\ker A$ and lies on the surface $M_\mu$. Let $\sigma_\mu$ be the surface measure on $M_\mu$, and for $x\in M_\mu^\circ$ let $\nu_x$ be the probability measure on the fiber $F_x$ with
--   $$\frac{d\nu_x}{d\nu^0_x}(W)=\frac{J_x(W)}{\mathbb E_{\nu^0_x}J_x},\qquad J_x(W)=\det(V^\top D_xV),$$
--   where $\nu^0_x$ is the reference law on $F_x$, $D_x=\mu X^{-2}$ and $V$ is any orthonormal basis matrix of $W$.
--
--   Then $x_\mu(A)$ has a density $p_\mu$ with respect to $\sigma_\mu$, and for every Borel $g:\mathrm{Gr}(k,n)\to[0,\infty]$,
--   $$\mathbb E\,g(\ker A)=\int_{M_\mu}p_\mu(x)\Big(\int g\,d\nu_x\Big)\,d\sigma_\mu(x).$$
--   That is, $(\nu_x)$ is a regular conditional distribution of $\ker A$ given $x_\mu(A)=x$.
--
--   The kernel of the random LP can thus be sampled in two stages: first the central point from its density, then a subspace from $\nu_x$, which is the reference (uniform) law on the fiber reweighted by $J_x$. This is what allows statements proved under the uniform subspace law of Theorem 6.8 to be transferred to the true conditional law.
--
--   **Formalization Note** A subspace $W$ is represented by its orthogonal projector $P_W$, and $\ker A$ by the projector onto the orthogonal complement of the row space of $A$. The density $p_\mu$ is existential, characterised by the requirement that $p_\mu\,\sigma_\mu$ is the law of $x_\mu(A)$. Full row rank of $A$ is not assumed; it holds almost surely.
--
--   Differences from the source:
--   - encoding: W ∈ Gr(k, n) and Borel g : Gr(k, n) → [0, ∞] → the orthogonal projector P_W (WainwrightHDS.NucNorm.projMat) in Fin n → Fin n → ℝ, and measurable g : (Fin n → Fin n → ℝ) → ℝ≥0∞; reason: W ↦ P_W is a homeomorphism of Gr(k, n) onto a closed set of matrices, so Borel functions on Gr(k, n) are exactly restrictions of Borel functions on matrices
--   - encoding: Haar measure on Gr(k − 1, E_x) in ν⁰_x → the span of the projections onto E_x of k − 1 independent standard Gaussian vectors; reason: the projected vectors are standard Gaussian in E_x, so the law of their span is O(E_x)-invariant and of dimension k − 1 a.s., hence Haar
--   - encoding: σ_µ, the induced (n − 1)-dimensional surface volume on M_µ → the (n − 1)-dimensional Hausdorff measure of EuclideanSpace ℝ (Fin n) restricted to M_µ; reason: on the smooth hypersurface M_µ it is a constant multiple of the surface volume, absorbed by the existential density
--   - encoding: the density p_µ of x_µ(A) with respect to σ_µ → ∃ measurable p with law of x_µ(A) = σ_µ.withDensity p; reason: this is how the paper introduces p_µ, and it determines p_µ σ_µ-a.e.; the explicit formula of Corollary 7.3 is not part of the theorem
--   - encoding: ν_x for fixed x ∈ M°_µ → ν_x defined by the same formula for every x, integrated over M_µ; reason: M_µ \ M°_µ = {1, µ1} is σ_µ-null
--   - encoding: 1 ≤ d ≤ n − 1 → 1 ≤ d and d + 1 ≤ n; reason: the same condition without natural-number truncation
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 7.7 and (104)-(105), p.65 (setting p.58; M_µ, σ_µ, E_x, F_x p.60; ν⁰_x p.61; J_x p.64; p_µ p.65)

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_xMu
import Definitions.Def_RandomLPIPM_rowSpace
import Definitions.Def_WainwrightHDS_NucNorm_projMat
import Definitions.Def_RandomLPIPM_Supplement_surfMeasure
import Definitions.Def_RandomLPIPM_Supplement_condLaw

open MeasureTheory
open scoped ENNReal

namespace RandomLPIPM.Supplement

/-- **Theorem 7.7 (Conditional law of the kernel).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 7.7, p.65 (setting §7, p.58;
objects §7.1–7.3, pp.58–64; the density `p_μ` in the paragraph before the theorem, p.65).

Let `A ∈ ℝ^{d×n}` have independent `N(0,1)` entries, `1 ≤ d ≤ n − 1`, `k = n − d`, and fix
`0 < μ < 1`. The central point `x_μ(A)` has a density `p_μ` with respect to the surface measure
`σ_μ` on `M_μ`, and for every Borel `g : Gr(k, n) → [0, ∞]`,
`E g(ker A) = ∫_{M_μ} p_μ(x) (∫ g dν_x) dσ_μ(x)` (105),
where `ν_x` is the reference fiber law `ν⁰_x` tilted by `J_x(W) = det(VᵀD_xV)` and normalised (104).
That is, `(ν_x)` is a regular conditional distribution of `ker A` given `x_μ(A) = x`.

**Formalization Note.** A subspace `W` is represented by its orthogonal projector `P_W`
(`WainwrightHDS.NucNorm.projMat`, read as a function `Fin n → Fin n → ℝ` with the Borel σ-algebra);
`ker A = (im Aᵀ)^⊥ = (rowSpace A)ᗮ`. Borel functions on `Gr(k, n)` are exactly the restrictions of
measurable functions on matrices, so `g` ranges over measurable `g : (Fin n → Fin n → ℝ) → ℝ≥0∞`.
`x_μ(A)` is the published `RandomLPIPM.xMu` (which equals `x_μ(ker A)` of (97)), read in
`EuclideanSpace ℝ (Fin n)`. `σ_μ` is `surfMeasure` (Euclidean `(n−1)`-Hausdorff measure on `M_μ`,
a constant multiple of the surface volume). `p_μ` is existential and is pinned down by the second
conjunct (`p_μ σ_μ` is the law of `x_μ(A)`), which is how the paper introduces it; its explicit
formula (Corollary 7.3) is not part of the theorem. The paper fixes `x ∈ M°_μ`; the integral in
(105) is over `M_μ`, and `M_μ \ M°_μ = {1, μ1}` is `σ_μ`-null, so the values of `ν_x` at the two
excluded points do not matter. Full row rank of `A` is not assumed (it holds almost surely). -/
theorem theorem_7_7 (n d : ℕ) (hd : 1 ≤ d) (hdn : d + 1 ≤ n) (μ : ℝ) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) :
    ∃ pμ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable pμ ∧
      (GaussianMatrix.gaussianMatrix d n).map
          (fun A => WithLp.toLp 2 (RandomLPIPM.xMu (Matrix.of A) μ)) =
        (surfMeasure n μ).withDensity pμ ∧
      ∀ g : (Fin n → Fin n → ℝ) → ℝ≥0∞, Measurable g →
        ∫⁻ A, g (Matrix.of.symm
            (WainwrightHDS.NucNorm.projMat (RandomLPIPM.rowSpace (Matrix.of A))ᗮ))
            ∂GaussianMatrix.gaussianMatrix d n =
          ∫⁻ x, pμ x * ∫⁻ P, g P ∂condLaw n (n - d) μ (WithLp.ofLp x) ∂surfMeasure n μ := by sorry

end RandomLPIPM.Supplement
