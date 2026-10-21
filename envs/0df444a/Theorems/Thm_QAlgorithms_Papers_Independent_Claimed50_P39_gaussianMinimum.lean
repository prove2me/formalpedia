-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_gaussianMinimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.gaussianMinimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:51:48.969208+00:00
-- url     : https://prove2.me/theorems/0820c3f3-04c7-4212-bdfb-038beb615e01
-- title:
--   Attained minimum over Gaussian inputs
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For a Gaussian density $\rho_G$ put $\alpha=\langle a\rangle$, $c=\langle a^\dagger a\rangle-|\alpha|^2+1/2$, $b=\langle a^2\rangle-\alpha^2$, and $d=c^2-|b|^2=\det\Gamma$, where $\Gamma=\left(\begin{smallmatrix}c&b\\\bar b&c\end{smallmatrix}\right)$. Its moment sums converge and $c\ge1/2$, $d\ge1/4$. Both outputs are Gaussian. Classical noise sends $(\alpha,c,b)$ to $(\alpha,c+n,b)$; thermal noise sends them to $(\sqrt\eta\alpha,\eta c+(1-\eta)(N+1/2),\eta b)$. Their entropies satisfy
--   $$S(\mathcal N_n(\rho_G))=g\!\left(\sqrt{d+n(n+2c)}-\tfrac12\right)\ge g(n),$$
--   $$S(\mathcal E_\eta^N(\rho_G))=g\!\left(\sqrt{\eta^2d+(1-\eta)(N+1/2)[(1-\eta)(N+1/2)+2\eta c]}-\tfrac12\right)\ge g((1-\eta)N).$$
--   Every coherent state is Gaussian and attains the respective Gaussian-restricted minimum. The Gaussian characteristic function uses linear term $z\bar\alpha-\bar z\alpha$, consistently with the Weyl convention.
--
--   This proves the Gaussian restriction only; it does not assume uncertainty inequalities as substitute hypotheses.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 5, §III, Eqs.(28)–(32): Gaussian-input minimum

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.5, Eqs.(28)–(32): Gaussian minima with coherent witnesses.
Printed: the Gaussian display uses -zeta0*zeta-dagger with zeta0=(mean a,mean a-dagger).
Changed: IsGaussian uses z*conjugate(alpha)-conjugate(z)*alpha for the linear term.
Why: this is the Weyl convention of Eq.(16); alpha=1,z=i gives phase +2i.
Covariance uncertainty and moment convergence are conclusions from the state,
not extra hypotheses replacing the channel result. Vacuum covariance is I/2. -/
theorem gaussianMinimum (eta N n : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hN : 0 ≤ N) (hn : 0 ≤ n) :
    (∀ X : B.FockOperator, IsGaussian X →
      FiniteEnergy X ∧
      Summable (fun j : ℕ => (Real.sqrt (j + 1 : ℝ) : ℂ) * X (B.fockKet j) (j + 1)) ∧
      Summable (fun j : ℕ => (Real.sqrt ((j + 1 : ℝ) * (j + 2 : ℝ)) : ℂ) * X (B.fockKet j) (j + 2)) ∧
      1 / 2 ≤ covarianceC X ∧ 1 / 4 ≤ covarianceDet X ∧
      IsGaussian (displacementNoiseChannel n X) ∧ IsGaussian (thermal eta N X) ∧
      meanA (displacementNoiseChannel n X) = meanA X ∧
      meanA (thermal eta N X) = (Real.sqrt eta : ℂ) * meanA X ∧
      covarianceC (displacementNoiseChannel n X) = covarianceC X + n ∧
      covarianceB (displacementNoiseChannel n X) = covarianceB X ∧
      covarianceC (thermal eta N X) = eta * covarianceC X + (1 - eta) * (N + 1 / 2) ∧
      covarianceB (thermal eta N X) = (eta : ℂ) * covarianceB X ∧
      fockEntropyNats (displacementNoiseChannel n X) = ENNReal.ofReal
        (g (Real.sqrt (covarianceDet X + n * (n + 2 * covarianceC X)) - 1 / 2)) ∧
      fockEntropyNats (thermal eta N X) = ENNReal.ofReal
        (g (Real.sqrt (eta ^ 2 * covarianceDet X + (1 - eta) * (N + 1 / 2) *
          ((1 - eta) * (N + 1 / 2) + 2 * eta * covarianceC X)) - 1 / 2))) ∧
    (∀ alpha : ℂ, IsGaussian (B.coherentProjector alpha) ∧
      IsLeast {s : ℝ≥0∞ | ∃ X, IsGaussian X ∧ s = fockEntropyNats (displacementNoiseChannel n X)}
        (fockEntropyNats (displacementNoiseChannel n (B.coherentProjector alpha))) ∧
      IsLeast {s : ℝ≥0∞ | ∃ X, IsGaussian X ∧ s = fockEntropyNats (thermal eta N X)}
        (fockEntropyNats (thermal eta N (B.coherentProjector alpha)))) ∧
    (∀ X, IsGaussian X → ENNReal.ofReal (g n) ≤ fockEntropyNats (displacementNoiseChannel n X) ∧
      ENNReal.ofReal (g ((1 - eta) * N)) ≤ fockEntropyNats (thermal eta N X)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
