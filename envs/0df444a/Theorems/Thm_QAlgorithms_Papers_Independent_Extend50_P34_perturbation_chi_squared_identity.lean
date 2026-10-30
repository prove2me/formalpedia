-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_perturbation_chi_squared_identity
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.perturbation_chi_squared_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:01:25.270965+00:00
-- url     : https://prove2.me/theorems/3c534ae2-2f9d-433b-89d1-28ffb17f7bd6
-- title:
--   Corollary 4.5
-- statement:
--   Let $d\ge1$, $n\ge0$, and $x\in\mathbb R^d$ satisfy $\sum_i x_i=0$ and $x_i\ge-1$. Put $Q_x(i)=(1+x_i)/d$. Then
--
--   $$d_{\chi^2}(\mathrm{SW}_{Q_x}^n,\mathrm{SW}_d^n)=\sum_{\substack{1\le|\mu|\le n\ell(\mu)\le d}}\frac{s_\mu(x)^2}{d^{\uparrow\mu}d^{|\mu|}}n^{\downarrow|\mu|}.$$
--
--   Equality at $x_i=-1$ is allowed, giving rank-deficient inputs. This expresses the statistical divergence using Schur polynomials.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 35, Corollary 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Corollary 4.5, arXiv:1501.05028v1, PDF p.35. Unlike Theorem 4.4, x_i≥-1 is required so Q_x is a probability distribution. -/
theorem perturbation_chi_squared_identity
    (d n : ℕ) (hd : 0 < d) (x : Fin d → ℝ)
    (hx : ∑ i, x i = 0) (hnonneg : ∀ i, -1 ≤ x i) :
    chiSq (swSpectrum (n := n) (perturbed x)) (swSpectrum (n := n) (unif d)) =
      ∑ k ∈ Finset.Icc 1 n, ∑ mu ∈ diagrams d k,
        schurAt mu x ^ 2 / (contentProduct d mu * (d : ℝ)^k) * falling n k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
