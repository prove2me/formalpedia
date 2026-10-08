-- Prove2me | Theorems.Thm_TikhonovHDD_Strong_lemma_A_1
-- name    : TikhonovHDD.Strong.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:18.201381+00:00
-- url     : https://prove2.me/theorems/7c6d6cab-e8b5-4a24-aba9-881321d8b37f
-- title:
--   Lemma A.1 — $\frac{1}{\varphi(t)}\int_\delta^t \varphi(s)f(s)\,ds \to 0$ for integrable $f\ge 0$ and nondecreasing $\varphi\to+\infty$
-- statement:
--   Let $\delta>0$ and let $f:(\delta,+\infty)\to\mathbb R$ be nonnegative, continuous and Lebesgue integrable on $(\delta,+\infty)$. Let $\varphi:[\delta,+\infty)\to[0,+\infty)$ be nondecreasing with $\lim_{t\to+\infty}\varphi(t)=+\infty$. Then
--   $$
--   \lim_{t\to+\infty}\frac{1}{\varphi(t)}\int_\delta^t\varphi(s)f(s)\,ds=0.
--   $$
--
--   This weighted averaging lemma (stated in Attouch, Chbani, Riahi as Lemma A.3) is the tool that turns integrability of a quantity into the vanishing of its weighted averages; in the paper it is used in the proof of Theorem 3.1 to show that $g(x(t))$ converges to $\min g$.
--
--   **Formalization Note** $f$ and $\varphi$ are functions $\mathbb R\to\mathbb R$; only their values on $(\delta,+\infty)$, respectively $[\delta,+\infty)$, enter the hypotheses. $1/\varphi(t)$ is written as the inverse $\varphi(t)^{-1}$, which is $0$ while $\varphi(t)=0$; since $\varphi(t)\to+\infty$, this affects only finitely long initial stretches and not the limit.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 29, Lemma A.1

import Mathlib

open Set Filter Topology

namespace TikhonovHDD.Strong

/-- Lemma A.1 (arXiv:1911.12845v2, p. 29). Let `δ > 0` and `f ∈ L¹((δ, +∞), ℝ)` be nonnegative
and continuous on `(δ, +∞)`. Let `φ : [δ, +∞) → [0, +∞)` be nondecreasing with
`φ(t) → +∞`. Then `(1/φ(t)) ∫_δ^t φ(s) f(s) ds → 0` as `t → +∞`. -/
theorem lemma_A_1 (δ : ℝ) (hδ : 0 < δ) (f φ : ℝ → ℝ)
    (hf_int : MeasureTheory.IntegrableOn f (Ioi δ))
    (hf_nonneg : ∀ t ∈ Ioi δ, 0 ≤ f t)
    (hf_cont : ContinuousOn f (Ioi δ))
    (hφ_nonneg : ∀ t ∈ Ici δ, 0 ≤ φ t)
    (hφ_mono : MonotoneOn φ (Ici δ))
    (hφ_lim : Tendsto φ atTop atTop) :
    Tendsto (fun t => (φ t)⁻¹ * ∫ s in δ..t, φ s * f s) atTop (𝓝 0) := by sorry

end TikhonovHDD.Strong
