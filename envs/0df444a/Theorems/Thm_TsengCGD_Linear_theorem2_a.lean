-- Prove2me | Theorems.Thm_TsengCGD_Linear_theorem2_a
-- name    : TsengCGD.Linear.theorem2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:54.797278+00:00
-- url     : https://prove2.me/theorems/389b3aca-b4a9-422e-b187-05723bd52ae7
-- title:
--   Theorem 2(a), corrected — $\|d_I(x^k)\| \le \max\{1,\sup_j\alpha^j\}\,C\,r^k$ for $k \in \mathcal T$ under the restricted Gauss–Seidel rule
-- statement:
--   Fix $n$ and constants $L\ge0$, $0<\underline\lambda\le\bar\lambda$. There is a constant $C>0$, depending only on $n$, $L$, $\underline\lambda$, $\bar\lambda$, with the following property. Consider any instance of problem (1) (with its standing assumptions) in which $\nabla f$ is $L$-Lipschitz on $\operatorname{dom}P$ (22), and any run $\{x^k\},\{H^k\},\{d^k\},\{\alpha^k\}$ of the CGD method with iterates in $\operatorname{dom}P$, satisfying Assumption 1 with $\underline\lambda,\bar\lambda$, with $\{\mathcal J^k\}$ chosen by the restricted Gauss–Seidel rule (12) along $\mathcal T\subseteq\{0,1,\dots\}$, and with $P$ block-separable with respect to every $\mathcal J^k$. If the stepsizes are bounded, $\alpha^j\le\bar\alpha$ for all $j$, then for every $k\in\mathcal T$
--   $$\|d_I(x^k)\|\ \le\ \max\{1,\bar\alpha\}\;C\;r^k,\qquad r^k=\sum_{\ell=k}^{\tau(k)-1}\|d^\ell\|.$$
--
--   The paper states $\|d_I(x^k)\|\le\sup_j\alpha^j\,C\,r^k$ without the block-separability hypothesis; we state the corrected form above. As printed, the bound fails twice. (1) With $n=1$, $P=0$, $f(x)=x^2/2$, $H^k=1$, $\mathcal T=\mathbb N$ and constant stepsizes $\alpha^k=\varepsilon$, it reads $|x^k|\le\varepsilon C|x^k|$, false for $\varepsilon<1/C$; the paper's proof gives the factor $\max\{1,\sup_j\alpha^j\}$. (2) With $n=2$, $\operatorname{dom}P=\{x_1+x_2\le0\}$, $P=0$ there, $f(x)=-x_1$, $H^k=I$, alternating blocks $\{1\},\{2\}$ and $x^0=0$, every coordinate step is blocked, so $r^0=0$ while $d_I(x^0)=(\tfrac12,-\tfrac12)$; the proof splits $d_I(x^k)$ over the blocks, which needs block-separability, as Theorem 2(b) assumes. Where the theorem is used, in (b), $\sup_j\alpha^j\le1$ and $P$ is block-separable, so (b) is unaffected.
--
--   The bound controls the optimality residual at the start of each Gauss–Seidel cycle by the length of the steps taken during the cycle; combined with the error bound (Assumption 2(a)) it drives the linear rate of Theorem 2(b).
--
--   **Formalization Note** The constant is quantified before the problem data, the run and $\mathcal T$, so it is uniform (it may depend on $n$, which is fixed). $\sup_j\alpha^j$ is replaced by an explicit upper bound $\bar\alpha$. The hypothesis $x^k\in\operatorname{dom}P$ for all $k$ is the domain of the method (the subproblem (6) is posed at $x\in\operatorname{dom}P$, and the proof uses $x^\ell,x^k\in\operatorname{dom}P$); with $\alpha^k\le1$ it follows from convexity. $\mathcal T=\{t_0<t_1<\cdots\}$ is a strictly increasing map with $t_0=0$, $k=t_i$ and $\tau(k)=t_{i+1}$. $d_I$ is the full direction (13) with $H=I$.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), pp. 405–406, Theorem 2(a) (corrected; see the statement)

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem theorem2_a {n : ℕ} (L lam lamBar : ℝ) :
    ∃ C > 0, ∀ (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
      (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
      (x d : ℕ → TsengCGD.Global.Vec n) (α : ℕ → ℝ) (t : ℕ → ℕ),
      TsengCGD.Global.Standing f D P c → GradLipOn f D L → TsengCGD.Global.IsCGDRun f D P c J H x d α →
      (∀ k, x k ∈ D) → TsengCGD.Global.Assumption1 H lam lamBar → RestrictedGaussSeidel J t →
      (∀ k, TsengCGD.Global.BlockSeparable D P (J k)) →
      ∀ abar : ℝ, (∀ j, α j ≤ abar) →
      ∀ i, ‖TsengCGD.Global.dI f D P c (x (t i))‖ ≤ max 1 abar * C * r t d i := by sorry

end TsengCGD.Linear
