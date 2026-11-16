-- Prove2me | Theorems.Thm_WildeQIT_Recover_recoveryCurve_hirschman_bound
-- name    : WildeQIT.Recover.recoveryCurve_hirschman_bound
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-16T01:41:28.683385+00:00
-- url     : https://prove2.me/theorems/75f25bf8-09fb-47f7-8234-4445ba03ec2b
-- title:
--   Stinespring interpolation bound for rotated Petz recovery fidelity
-- statement:
--   Let $\rho$ be a density matrix, $\sigma\ge0$ a positive semidefinite matrix, and $\mathcal N$ a finite dimensional quantum channel with Stinespring isometry $U$. All complex powers are restricted to the support, so no invertibility assumption is made. Define
--   $$G(z)=\bigl(\mathcal N(\rho)^{z/2}\mathcal N(\sigma)^{-z/2}\otimes I_E\bigr)U\sigma^{z/2}\rho^{1/2}.$$
--   For $0<\theta<1$ and $p_\theta=2/(1+\theta)$, write $\|A\|_p=(\operatorname{Tr}(A^\dagger A)^{p/2})^{1/p}$. Then
--   $$\log\|G(\theta)\|_{p_\theta}\le\int_{\mathbb R}\beta_\theta(t)\log\!\left(\sqrt{F\!\left(\rho,\mathcal R^{t/2}_{\sigma,\mathcal N}(\mathcal N(\rho))\right)}^{\;\theta}\right)\,dt.$$
--   Here $\mathcal R^s_{\sigma,\mathcal N}$ is the rotated Petz map, $F$ is the fidelity, and $\beta_\theta$ is the Hirschman density. The logarithm is extended by $\log0=-\infty$ and the integral is the signed extended integral of its positive and negative parts.
--
--   This is the finite parameter recoverability bound, before taking the relative entropy limit. It combines rectangular matrix interpolation with the actual Stinespring recovery curve. It does not assert the entropy limit or the averaged universal recovery theorem.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §12.5, Eqs.(12.104)–(12.108), pp.378–379; https://arxiv.org/abs/1106.1445v8 . Proof includes the analytic curve and both endpoint estimates for support powers of possibly singular states.

import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_WildeQIT_Recover_renyiDelta
import Definitions.Def_WildeQIT_Recover_rotatedPetz
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
open Matrix WildeQIT
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped MatrixOrder ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator Kronecker

namespace WildeQIT.Recover
theorem recoveryCurve_hirschman_bound {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    let G : ℂ → Matrix (b×N.ι) a ℂ := fun z =>
      letI : DecidableEq N.ι := Classical.decEq _
      ((supportPow (N.apply ρ) (z/2)*supportPow (N.apply σ) (-(z/2))) ⊗ₖ (1 : Matrix N.ι N.ι ℂ))*
        isometricExt N*supportPow σ (z/2)*supportPow ρ (1/2)
    let p : ℝ := 2/(1+θ)
    extendedLog (((cfc (fun x : ℝ => x^(p/2)) ((G θ)ᴴ*G θ)).trace.re)^(1/p)) ≤
      upperLogIntegral (fun t => (betaDensity θ t : EReal)*
        extendedLog ((rootFidelity ρ (rotatedPetz σ N (t/2) (N.apply ρ)))^θ)) := by sorry
end WildeQIT.Recover
