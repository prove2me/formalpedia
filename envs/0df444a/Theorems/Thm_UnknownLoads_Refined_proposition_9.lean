-- Prove2me | Theorems.Thm_UnknownLoads_Refined_proposition_9
-- name    : UnknownLoads.Refined.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:01.987876+00:00
-- url     : https://prove2.me/theorems/ed37e784-f8e2-4700-b6e8-6ee4e97433c6
-- title:
--   Proposition 9 — below the threshold j, subsequential limits obey the infinite-server ODE and v(j+1) decays
-- statement:
--   Fix $\omega\in\Omega_T$ and an increasing sequence $\mathcal K$ of system indices. Suppose that
--
--   (a) $\{q_k(\omega):k\in\mathcal K\}$ converges to $q\in D_{\mathbb R^{\mathbb N}}[0,T]$ in $\varrho$;
--
--   (b) there are $j\in\{i\Delta:i\ge1\}$ and $0\le t_0<t_1\le T$ with $\ell_k(\omega,t)\le j$ and $q_k(\omega,t,j)<1$ for all $t\in[t_0,t_1]$ and $k\in\mathcal K$;
--
--   and that $u(t_0)>0$. Then for all $i>j$ the coordinate $q(i)$ is differentiable on $(t_0,t_1)$ with
--   $$
--   \dot q(t,i)=-\mu i\,[q(t,i)-q(t,i+1)],\qquad t\in(t_0,t_1),
--   $$
--   and $\{v_k(\omega,j+1):k\in\mathcal K\}$ converges uniformly over $[0,T]$ to a function $v(j+1)$ with
--   $$
--   v(t,j+1)<u(t_0)e^{-\mu(t-t_0)}\qquad\text{for all }t\in[t_0,t_1].
--   $$
--
--   While the threshold stays at most $j$, no task joins a pool with $j$ or more tasks, so the tail beyond $j$ drains at least exponentially; this drives (6c) and the proof of (6a).
--
--   Throughout, "for each $\omega\in\Omega_T$" is rendered as: for every constant $B_T$ and every outcome $\omega$ satisfying the nice-path predicate $\mathrm{IsNicePath}(B_T,\omega)$ of Proposition 7 (the standing initial conditions, the equations (9a)–(9b) with simple events for every $n\ge1$, the relative-compactness property of Proposition 4, (11) with some $n_T(\omega)$, and (12a)–(12c) for every $\gamma\in[0,1/2)$). Proposition 7 states that this predicate holds almost surely for some $B_T>0$.
--
--   **Formalization Note** The hypothesis $u(t_0)>0$ is added: if $u(t_0)=0$ (e.g. an initially empty system at $t_0=0$) both sides of the strict inequality vanish at $t=t_0$ and the paper's statement fails; both uses in the paper have $u(t_0)>0$. $\mathcal K$ is a strictly increasing $\varphi:\mathbb N\to\mathbb N$ with $\varphi(0)\ge1$; (a) is coordinatewise uniform convergence on $[0,T]$; differentiability is `HasDerivAt` at each interior point.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, pp. 28–30, Proposition 9

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem proposition_9 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (BT : ℕ) (ω : Ω) (hω : sys.IsNicePath BT ω)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hφ₀ : 1 ≤ φ 0)
    (y : ℝ → ℕ → ℝ)
    (ha : ∀ i, TendstoUniformlyOn (fun k t => sys.q (φ k) ω t i) (fun t => y t i) atTop
      (Icc 0 D.T))
    (j : ℕ) (hj : ∃ i : ℕ, 1 ≤ i ∧ j = i * D.Δ) (t₀ t₁ : ℝ)
    (ht₀ : 0 ≤ t₀) (ht₀₁ : t₀ < t₁) (ht₁ : t₁ ≤ D.T)
    (hb : ∀ t ∈ Icc t₀ t₁, ∀ k, sys.ℓ (φ k) ω t ≤ j ∧ sys.q (φ k) ω t j < 1)
    (hu : 0 < D.fluidU sys.q0 t₀) :
    (∀ i, j < i → ∀ t ∈ Ioo t₀ t₁,
      HasDerivAt (fun s => y s i) (-(D.mu * i) * (y t i - y t (i + 1))) t) ∧
    ∃ v : ℝ → ℝ,
      TendstoUniformlyOn (fun k t => sys.tailMass (φ k) ω t (j + 1)) v atTop (Icc 0 D.T) ∧
      ∀ t ∈ Icc t₀ t₁, v t < D.fluidU sys.q0 t₀ * Real.exp (-D.mu * (t - t₀)) := by sorry

end UnknownLoads.Refined
