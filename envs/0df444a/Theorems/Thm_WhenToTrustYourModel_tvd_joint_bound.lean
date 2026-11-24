-- Prove2me | Theorems.Thm_WhenToTrustYourModel_tvd_joint_bound
-- name    : WhenToTrustYourModel.tvd_joint_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:08:46.970801+00:00
-- url     : https://prove2.me/theorems/b5d3d157-3953-4ccd-8657-0f65d543e0d4
-- title:
--   Lemma B.1: TVD of joint distributions
-- statement:
--   Let $X$ and $Y$ be finite sets, let $p_1,p_2$ be distributions on $X$, and for every $x\in X$ let $p_1(\cdot\mid x)$ and $p_2(\cdot\mid x)$ be distributions on $Y$. Form the joint distributions $p_i(x,y)=p_i(x)\,p_i(y\mid x)$. Then
--
--   $$D_{TV}\big(p_1(x,y)\|p_2(x,y)\big)\le D_{TV}\big(p_1(x)\|p_2(x)\big)+\max_x D_{TV}\big(p_1(y\mid x)\|p_2(y\mid x)\big),$$
--
--   and, more tightly,
--
--   $$D_{TV}\big(p_1(x,y)\|p_2(x,y)\big)\le D_{TV}\big(p_1(x)\|p_2(x)\big)+E_{x\sim p_1}\big[D_{TV}\big(p_1(y\mid x)\|p_2(y\mid x)\big)\big].$$
--
--   This is the step that turns a policy divergence plus a model error into a divergence of the joint state-action-next-state distribution in all later bounds.
-- source:
--   Janner, Fu, Zhang and Levine, When to Trust Your Model: Model-Based Policy Optimization, arXiv:1906.08253v3 (NeurIPS 2019), Appendix B, Lemma B.1, p. 15

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

open Finset

namespace WhenToTrustYourModel

theorem tvd_joint_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (p₁ p₂ : X → ℝ) (hp₁ : IsDist p₁) (hp₂ : IsDist p₂)
    (q₁ q₂ : X → Y → ℝ) (hq₁ : ∀ x, IsDist (q₁ x)) (hq₂ : ∀ x, IsDist (q₂ x)) :
    tvDist (jointDist p₁ q₁) (jointDist p₂ q₂) ≤ tvDist p₁ p₂ + (⨆ x, tvDist (q₁ x) (q₂ x)) ∧
    tvDist (jointDist p₁ q₁) (jointDist p₂ q₂) ≤
      tvDist p₁ p₂ + ∑ x, p₁ x * tvDist (q₁ x) (q₂ x) := by sorry

end WhenToTrustYourModel
