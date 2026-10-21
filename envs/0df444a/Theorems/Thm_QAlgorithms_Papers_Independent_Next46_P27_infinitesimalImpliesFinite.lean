-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_infinitesimalImpliesFinite
-- name    : QAlgorithms.Papers.Independent.Next46.P27.infinitesimalImpliesFinite
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:21:59.075788+00:00
-- url     : https://prove2.me/theorems/cababb09-c351-4253-83ca-4f8c5a54fe33
-- title:
--   The infinitesimal conjecture implies the finite additive-noise conjecture
-- statement:
--   On the full single-mode Fock space, let $S$ be extended von Neumann entropy in nats and $\Phi_v$ the exact Gaussian displacement channel. For a density $X$ of finite entropy and $\gamma>0$, define the lower right Dini entropy-production rate by
--
--   $$R_\gamma(X)=\liminf_{t\downarrow0}\frac{S(\Phi_{\gamma t}(X))-S(X)}{t}.$$
--
--   Let $\tau_M$ be the thermal density of mean photon number $M\ge0$, including the vacuum at $M=0$, and let $g(M)=(M+1)\log(M+1)-M\log M$, with $0\log0=0$. Assume the infinitesimal conjecture: for every $\gamma>0$, every $M\ge0$, and every density $X$ with $S(X)=g(M)$, one has $R_\gamma(\tau_M)\le R_\gamma(X)$. Then
--
--   $$\forall v>0\ \forall X\text{ a density},\qquad g(v)\le S(\Phi_v(X)).$$
--
--   The conclusion is the finite additive-noise vacuum conjecture, with no input-energy or input-entropy restriction. Only this forward implication is asserted.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 2, Section I: conditional infinitesimal-to-finite implication

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.2, Section I: forward infinitesimal-to-finite implication only.
The conclusion quantifies over all densities, including infinite-energy inputs. -/
theorem infinitesimalImpliesFinite (h : InfinitesimalConjecture) :
    ∀ v : ℝ, 0 < v → A.ClassicalEntropyConjecture v := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
