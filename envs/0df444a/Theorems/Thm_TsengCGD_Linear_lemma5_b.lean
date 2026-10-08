-- Prove2me | Theorems.Thm_TsengCGD_Linear_lemma5_b
-- name    : TsengCGD.Linear.lemma5_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:44.087049+00:00
-- url     : https://prove2.me/theorems/4cfbefab-f7c7-41fe-94a0-4dd47a286a09
-- title:
--   Lemma 5(b) — the Armijo descent condition (23) holds for $0 \le \alpha \le \min\{1, 2\lambda(1-\sigma+\sigma\gamma)/L\}$
-- statement:
--   Consider problem (1): $F_c=f+cP$ with $c>0$, $P$ proper, convex, lower semicontinuous and $f$ continuously differentiable on an open set containing $\operatorname{dom}P$. Let $x\in\operatorname{dom}P$, $H\succ0_n$, $\mathcal J\subseteq\mathcal N$ nonempty, $d=d_H(x;\mathcal J)$, $\gamma\in[0,1)$ and $\Delta=\nabla f(x)^Td+\gamma d^THd+cP(x+d)-cP(x)$.
--
--   Suppose $\nabla f$ is $L$-Lipschitz on $\operatorname{dom}P$ for some $L\ge0$ (condition (22)) and $H\succeq\underline\lambda I$ with $\underline\lambda>0$. Then for every $\sigma\in(0,1)$ the descent condition
--   $$F_c(x+\alpha d)-F_c(x)\ \le\ \sigma\alpha\Delta\qquad(23)$$
--   holds whenever $0\le\alpha\le\min\{1,\,2\underline\lambda(1-\sigma+\sigma\gamma)/L\}$ (read as $0\le\alpha\le1$ when $L=0$).
--
--   The lemma gives a stepsize, independent of $x$, at which the Armijo test (9) always passes; it is what makes the Armijo stepsizes bounded away from zero in Theorem 1(f).
--
--   **Formalization Note** The step range is stated as $0\le\alpha\le1$ and $\alpha L\le2\underline\lambda(1-\sigma+\sigma\gamma)$, which is the paper's range for $L>0$ and $[0,1]$ for $L=0$; the literal Lean `min 1 (… / L)` would be $0$ at $L=0$. The conclusion includes $x+\alpha d\in\operatorname{dom}P$, so that both sides of (23) are finite. $H\succeq\underline\lambda I$ is stated as $\underline\lambda\|z\|^2\le z^THz$ for all $z$.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), pp. 397–398, Lemma 5(b), (22), (23)

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem lemma5_b {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) (hJ : J.Nonempty) (d : TsengCGD.Global.Vec n)
    (hd : TsengCGD.Global.IsDir f D P c H x J d) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (L : ℝ) (hL : GradLipOn f D L) (lam : ℝ) (hlam : 0 < lam)
    (hHlam : ∀ z : TsengCGD.Global.Vec n, lam * ‖z‖ ^ 2 ≤ TsengCGD.Global.qf H z)
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hαL : α * L ≤ 2 * lam * (1 - σ + σ * γ)) :
    x + α • d ∈ D ∧ TsengCGD.Global.Fc f P c (x + α • d) - TsengCGD.Global.Fc f P c x ≤ σ * α * TsengCGD.Global.Delta f P c γ H x d := by sorry

end TsengCGD.Linear
