-- Prove2me | Theorems.Thm_PINNConvergence_elliptic_stability
-- name    : PINNConvergence.elliptic_stability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:09:41.201812+00:00
-- url     : https://prove2.me/theorems/08d1b65d-ef97-439e-a681-ea1fbb038265
-- title:
--   Lemma D.1 (as proved): existence, uniqueness and $C^0$ stability for the elliptic Dirichlet problem
-- statement:
--   Let $U\subset\mathbb{R}^d$, $d\ge1$, be a bounded domain, and let $\lambda_0$, $v$ and functions $\tilde b^i$ be given. There is a constant $C>0$, depending only on $U$, $\tilde b$, $\lambda_0$ and $v$, such that the following holds. Suppose the coefficients $a,b,c,e$ and the data $f,g$ satisfy Assumption 3.3 with these $\lambda_0,v$ (and some $\Lambda$), that $\tilde c=\sum_iD_ib^i+e\le0$ in $U$, and that $\sum_jD_ja^{ij}+b^i+c^i=\tilde b^i$ in $U$. Then:
--
--   1. the Dirichlet problem $\mathcal L[u]=f$ in $U$, $u=g$ on $\partial U$ has a classical solution $u^*\in C^2(U)\cap C^0(\overline U)$, unique on $\overline U$;
--   2. for every $h\in C^2(U)\cap C^0(\overline U)$ with $\mathcal L[h]\in C^{0,\alpha}(U)$ and $h\in C^{0,\alpha}(\partial U)$,
--
--   $$\|u^*-h\|_{C^0(U)}\le C\big(\|f-\mathcal L[h]\|_{C^0(U)}+\|g-h\|_{C^0(\partial U)}\big).$$
--
--   The estimate turns uniform convergence of the residuals (Theorem 3.2) into uniform convergence of the networks (Theorem 3.3).
--
--   **Formalization Note** This is the lemma as its proof establishes it. The paper requires only $h\in C^0(U)$. The proof needs $h\in C^2(U)$, for $\mathcal L[h]$ to be defined classically, and $h\in C^0(\overline U)$, so that $u^*-h+\xi$ is continuous up to $\partial U$. Without continuity up to the boundary the estimate fails. On the unit disc with $\mathcal L=\Delta$, take $h=u^*+1$ in $U$ and $h=g$ on $\partial U$. The right side is $0$ and the left side is $1$. The dependence of $C$ is encoded by choosing $C$ after $U,\lambda_0,v,\tilde b$ and before the coefficients, the data and $h$.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Appendix D, Lemma D.1, eq. (D.1), p. 26

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem elliptic_stability {d : ℕ} (hd : 1 ≤ d) (U : Set (Rd d)) (hU : IsBoundedDomain U)
    (lam0 v : ℝ) (bt : Fin d → Rd d → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (a : Fin d → Fin d → Rd d → ℝ) (b c : Fin d → Rd d → ℝ)
      (e f g : Rd d → ℝ) (Lam : ℝ), EllipticAssumption α U a b c e f g lam0 Lam v →
      (∀ x ∈ U, ctilde b e x ≤ 0) → (∀ i, ∀ x ∈ U, btilde a b c i x = bt i x) →
      (∃ u, IsClassicalSol U a b c e f g u ∧
        ∀ w, IsClassicalSol U a b c e f g w → Set.EqOn w u (closure U)) ∧
      ∀ u, IsClassicalSol U a b c e f g u → ∀ h : Rd d → ℝ, ContDiffOn ℝ 2 h U →
        ContinuousOn h (closure U) → IsHolderCk 0 α U (ellipticOp a b c e h) →
        IsHolderCk 0 α (frontier U) h →
        supNorm U (u - h) ≤ ENNReal.ofReal C *
          (supNorm U (f - ellipticOp a b c e h) + supNorm (frontier U) (g - h)) := by sorry

end PINNConvergence
