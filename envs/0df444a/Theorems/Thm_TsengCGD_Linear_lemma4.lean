-- Prove2me | Theorems.Thm_TsengCGD_Linear_lemma4
-- name    : TsengCGD.Linear.lemma4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:43.944613+00:00
-- url     : https://prove2.me/theorems/25a923dc-9b3d-47f3-a5c9-f3c71e5629d4
-- title:
--   Lemma 4 — Hölder-type Lipschitz dependence of the coordinate subproblem's minimizer on the linear term
-- statement:
--   Let $c>0$ and let $P:\Re^n\to(-\infty,\infty]$ be proper, convex and lower semicontinuous. Let $h:\Re^n\to\Re$ be continuously differentiable and satisfy, for some $\rho>0$ and $p>1$,
--   $$(\nabla h(u)-\nabla h(v))^T(u-v)\ \ge\ \rho\,\|u-v\|_p^p\qquad\text{for all }u,v\in\Re^n,$$
--   and let $q$ be the conjugate exponent, $\tfrac1p+\tfrac1q=1$. Fix $x\in\operatorname{dom}P$, a nonempty index set $\mathcal J\subseteq\mathcal N$, and two vectors $\bar g,\tilde g\in\Re^n$. Let $\bar d$ minimize $\bar g^Td+h(d)+cP(x+d)$ and $\tilde d$ minimize $\tilde g^Td+h(d)+cP(x+d)$, both over the vectors $d$ with $d_j=0$ for $j\notin\mathcal J$. Then
--   $$\|\bar d-\tilde d\|_p\ \le\ \rho^{-q/p}\,\|\bar g_{\mathcal J}-\tilde g_{\mathcal J}\|_q^{q/p}.$$
--
--   The lemma says that the coordinate subproblem's solution moves Hölder-continuously with its linear coefficients; with $h(u)=\|u\|^2/2$, $p=q=2$, $\rho=1$ it is the 1-Lipschitz dependence of $d_I(x;\mathcal J)$ on $\nabla f(x)_{\mathcal J}$ that the proof of Theorem 2(a) uses.
--
--   **Formalization Note** $P$ is the pair $(D,P)$ with $D=\operatorname{dom}P$. A minimizer is a vector supported on $\mathcal J$ with $x+d\in D$ and objective value no larger than that of any other such vector (the others have value $+\infty$); the bound is asserted for every pair of minimizers, which is the paper's statement since the minimizers are unique. Coordinates are 0-based (`Fin n`), and $\|\cdot\|_p$, $\|\cdot\|_q$ are the explicit sums of `rpow`s, of nonnegative bases.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 396, Lemma 4

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem lemma4 {n : ℕ} (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) (hc : 0 < c)
    (h : TsengCGD.Global.Vec n → ℝ) (hh : ContDiff ℝ 1 h) (ρ p q : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (hq : 1 / p + 1 / q = 1)
    (hmono : ∀ u v : TsengCGD.Global.Vec n, ρ * pNorm p (u - v) ^ p ≤ ⟪gradient h u - gradient h v, u - v⟫)
    (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty) (gb gt db dt : TsengCGD.Global.Vec n)
    (hdb : TsengCGD.Global.SupportedOn J db ∧ x + db ∈ D ∧ ∀ d', TsengCGD.Global.SupportedOn J d' → x + d' ∈ D →
      ⟪gb, db⟫ + h db + c * P (x + db) ≤ ⟪gb, d'⟫ + h d' + c * P (x + d'))
    (hdt : TsengCGD.Global.SupportedOn J dt ∧ x + dt ∈ D ∧ ∀ d', TsengCGD.Global.SupportedOn J d' → x + d' ∈ D →
      ⟪gt, dt⟫ + h dt + c * P (x + dt) ≤ ⟪gt, d'⟫ + h d' + c * P (x + d')) :
    pNorm p (db - dt) ≤ ρ ^ (-q / p) * pNormOn q J (gb - gt) ^ (q / p) := by sorry

end TsengCGD.Linear
