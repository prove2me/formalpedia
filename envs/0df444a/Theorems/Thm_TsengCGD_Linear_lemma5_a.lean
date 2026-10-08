-- Prove2me | Theorems.Thm_TsengCGD_Linear_lemma5_a
-- name    : TsengCGD.Linear.lemma5_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:57.88202+00:00
-- url     : https://prove2.me/theorems/4768beb1-818e-42d0-9001-3fcfd85e11f3
-- title:
--   Lemma 5(a) — variational inequality for the step $x' = x + \alpha d$ under block-separability
-- statement:
--   Consider problem (1): $F_c=f+cP$ with $c>0$, $P$ proper, convex, lower semicontinuous and $f$ continuously differentiable on an open set containing $\operatorname{dom}P$. Let $x\in\operatorname{dom}P$, $H\succ0_n$, $\mathcal J\subseteq\mathcal N$ nonempty, $d=d_H(x;\mathcal J)$ the direction (6), $g=\nabla f(x)$, and $\gamma\in[0,1)$; put $\Delta=g^Td+\gamma d^THd+cP(x+d)-cP(x)$.
--
--   Suppose $P$ is block-separable with respect to $\mathcal J$, $P(x)=P_{\mathcal J}(x_{\mathcal J})+P_{\mathcal J^C}(x_{\mathcal J^C})$. Then for every $\bar x\in\Re^n$, every $\alpha\in(0,1]$ and $x'=x+\alpha d$,
--   $$(g+Hd)_{\mathcal J}^T(x'-\bar x)_{\mathcal J}+cP_{\mathcal J}(x'_{\mathcal J})-cP_{\mathcal J}(\bar x_{\mathcal J})\ \le\ (\alpha-1)\big[(1-\gamma)d^THd+\Delta\big].$$
--
--   This inequality compares a partial step with an arbitrary point on the block $\mathcal J$; it is the per-block estimate that the linear convergence proof of Theorem 2(b) sums over a Gauss–Seidel cycle.
--
--   **Formalization Note** The left side involves the particular summand $P_{\mathcal J}$, so the statement holds for every decomposition (20) of $P$; a decomposition is given by two proper convex lsc functions on $\Re^n$, one depending only on $x_{\mathcal J}$ (with its own effective domain), the other only on $x_{\mathcal J^C}$. When $\bar x_{\mathcal J}\notin\operatorname{dom}P_{\mathcal J}$ the left side is $-\infty$ and the inequality is empty, so $\bar x$ ranges over $\operatorname{dom}P_{\mathcal J}$. $d$ is any minimizer of (6) (it is unique). Coordinates are 0-based; $d^THd$ is the quadratic form of the matrix $H$.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 397, Lemma 5(a)

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem lemma5_a {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) (hJ : J.Nonempty) (d : TsengCGD.Global.Vec n)
    (hd : TsengCGD.Global.IsDir f D P c H x J d) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (DJ : Set (TsengCGD.Global.Vec n)) (PJ : TsengCGD.Global.Vec n → ℝ) (DJC : Set (TsengCGD.Global.Vec n)) (PJC : TsengCGD.Global.Vec n → ℝ)
    (hw : TsengCGD.Global.IsBlockSepWitness D P J DJ PJ DJC PJC)
    (xbar : TsengCGD.Global.Vec n) (hxbar : xbar ∈ DJ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ j ∈ J, (gradient f x j + (H *ᵥ WithLp.ofLp d) j) * ((x + α • d) j - xbar j))
        + c * PJ (x + α • d) - c * PJ xbar
      ≤ (α - 1) * ((1 - γ) * TsengCGD.Global.qf H d + TsengCGD.Global.Delta f P c γ H x d) := by sorry

end TsengCGD.Linear
