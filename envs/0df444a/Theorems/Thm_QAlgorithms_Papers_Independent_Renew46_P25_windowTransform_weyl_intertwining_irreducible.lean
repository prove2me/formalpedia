-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P25_windowTransform_weyl_intertwining_irreducible
-- name    : QAlgorithms.Papers.Independent.Renew46.P25.windowTransform_weyl_intertwining_irreducible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:42:36.601856+00:00
-- url     : https://prove2.me/theorems/7de49234-28b3-41ba-bedb-1e2226ebc6e3
-- title:
--   Weyl intertwining and irreducibility on each window range
-- statement:
--   Let $n\ge1$ and let $\phi\in\mathcal S(\mathbb R^n)$ satisfy $\|\phi\|_2^2=1$. The kernel $U_\phi f(x,p)=(2\pi)^{-n/2}e^{ip\cdot x/2}\int e^{-ip\cdot y}\phi(x-y)f(y)\,dy$ extends to an isometric embedding $U_\phi:L^2(\mathbb R^n)\to L^2(\mathbb R^{2n})$ with closed range $\mathcal H_\phi$. Let $T(z_0)f(x)=e^{i(p_0\cdot x-p_0\cdot x_0/2)}f(x-x_0)$ and $T_{\rm ph}(z_0)F(z)=e^{-i\sigma(z,z_0)/2}F(z-z_0)$, for $z_0=(x_0,p_0)$. Then
--
--   $$T_{\rm ph}(z_0)U_\phi=U_\phi T(z_0).$$
--
--   Moreover the Heisenberg representation $\rho(z,t)=e^{it}T_{\rm ph}(z)$ is irreducible on $\mathcal H_\phi$: a closed complex subspace $K\subseteq\mathcal H_\phi$ invariant under every $\rho(z,t)$ is either $\{0\}$ or $\mathcal H_\phi$.
--
--   The L2 maps are specified by their actual formulas, with their existence a conclusion. This retains (91) and the proof's final sentence without asserting the false full-center identity (89) or ambient irreducibility. Here $\sigma((x,p),(x',p'))=p\cdot x'-p'\cdot x$, and the range $\mathcal H_\phi$ is invariant under every $\rho(z,t)$. The group product is $(z,t)(w,s)=(z+w,t+s+\sigma(z,w)/2)$.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, PDF p. 34, Proposition 18 proof (91): Weyl intertwining and irreducibility on each Hφ

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25

noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF pp.34-35, Proposition 18 proof, (91), and its final irreducibility
sentence: zero-center intertwining and irreducibility on the actual H_phi.
The isometry is realized by the fixed Schwartz kernel in windowTransform;
its existence is a conclusion. The ambient L2 representation is not declared
irreducible and the false central-character identity (89) is not used. -/
theorem windowTransform_weyl_intertwining_irreducible (n : ℕ) (hn : 0 < n)
    (phi : SchwartzMap (ConfigurationEuclidean n) ℂ) (hphi : ‖phi.toLp 2 volume‖ ^ 2 = 1) :
    ∃ (U : ConfigurationEuclideanL2 n →ₗᵢ[ℂ] PhaseGroupedL2 n)
      (rho : (PhaseSpaceGrouped n × ℝ) → (PhaseGroupedL2 n ≃ₗᵢ[ℂ] PhaseGroupedL2 n))
      (tau : PhaseSpaceGrouped n → (ConfigurationEuclideanL2 n ≃ₗᵢ[ℂ] ConfigurationEuclideanL2 n)),
      (∀ f : SchwartzMap (ConfigurationEuclidean n) ℂ,
        (fun z => U (f.toLp 2 volume) z) =ᵐ[volume] windowTransform phi f) ∧
      IsClosed (Set.range U) ∧
      (∀ g f, (fun z => rho g f z) =ᵐ[volume] phaseHeisenberg g f) ∧
      (∀ z0 f, (fun x => tau z0 f x) =ᵐ[volume] configurationTranslation z0 f) ∧
      (∀ z0 f, rho (z0, 0) (U f) = U (tau z0 f)) ∧
      rho (0, 0) = LinearIsometryEquiv.refl ℂ (PhaseGroupedL2 n) ∧
      (∀ g h f, rho g (rho h f) = rho (heisenbergProduct g h) f) ∧
      (∀ (g : PhaseSpaceGrouped n × ℝ) (f : PhaseGroupedL2 n),
        f ∈ LinearMap.range U.toLinearMap → rho g f ∈ LinearMap.range U.toLinearMap) ∧
      (∀ K : Submodule ℂ (PhaseGroupedL2 n),
        IsClosed (K : Set (PhaseGroupedL2 n)) → K ≤ LinearMap.range U.toLinearMap →
        (∀ (g : PhaseSpaceGrouped n × ℝ) (f : PhaseGroupedL2 n), f ∈ K → rho g f ∈ K) →
        K = ⊥ ∨ K = LinearMap.range U.toLinearMap) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P25

end
