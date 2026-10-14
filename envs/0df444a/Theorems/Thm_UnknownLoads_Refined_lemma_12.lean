-- Prove2me | Theorems.Thm_UnknownLoads_Refined_lemma_12
-- name    : UnknownLoads.Refined.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:01.000843+00:00
-- url     : https://prove2.me/theorems/f0afb5cc-eb40-477c-b604-238545fd7340
-- title:
--   Lemma 12 — lower bound on the growth of Σ_{i≤j} q_k(i) while ℓ_k ≤ j and q_k(j) < 1
-- statement:
--   Fix $\omega\in\Omega_T$ and $j\in\{i\Delta:i\ge1\}$. Let $\mathcal K$ be an increasing sequence of system indices and let $0\le\tau_{k,1}\le\tau_{k,2}\le T$ ($k\in\mathcal K$) be times with
--   $$
--   \ell_k(\omega,t)\le j\quad\text{and}\quad q_k(\omega,t,j)<1\qquad\text{for all }t\in[\tau_{k,1},\tau_{k,2})\text{ and }k\in\mathcal K.
--   $$
--   Then for all $t\in[\tau_{k,1},\tau_{k,2}]$ and $k\in\mathcal K$,
--   $$
--   \sum_{i=1}^jq_k(\omega,t,i)-\sum_{i=1}^jq_k(\omega,\tau_{k,1},i)\ \ge\ \int_{\tau_{k,1}}^t[\lambda(s)-\mu j]\,ds-2\sup_{s\in[0,T]}|\delta_k(\omega,s,j)| ,
--   $$
--   with $\delta_k$ the process (16).
--
--   While every arrival goes to a pool with fewer than $j$ tasks, the mass in the first $j$ columns grows at least at rate $\lambda-\mu j$, up to the fluctuation term $\delta_k$.
--
--   Throughout, "for each $\omega\in\Omega_T$" is rendered as: for every constant $B_T$ and every outcome $\omega$ satisfying the nice-path predicate $\mathrm{IsNicePath}(B_T,\omega)$ of Proposition 7 (the standing initial conditions, the equations (9a)–(9b) with simple events for every $n\ge1$, the relative-compactness property of Proposition 4, (11) with some $n_T(\omega)$, and (12a)–(12c) for every $\gamma\in[0,1/2)$). Proposition 7 states that this predicate holds almost surely for some $B_T>0$.
--
--   **Formalization Note** The "random times" are, for the fixed $\omega$, two real sequences indexed by $k$. The supremum is rendered through upper bounds: the inequality is asserted with $2M$ in place of $2\sup|\delta_k|$ for every $M$ bounding $|\delta_k(\omega,s,j)|$ on $[0,T]$ (equivalent, and free of a real `sSup` of an unbounded set). $\mathcal K$ is a strictly increasing $\varphi$ with $\varphi(0)\ge1$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 33, Lemma 12

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem lemma_12 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α)
    (BT : ℕ) (ω : Ω) (hω : sys.IsNicePath BT ω)
    (j : ℕ) (hj : ∃ i : ℕ, 1 ≤ i ∧ j = i * D.Δ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hφ₀ : 1 ≤ φ 0)
    (τ₁ τ₂ : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ₁ k ∧ τ₁ k ≤ τ₂ k ∧ τ₂ k ≤ D.T)
    (hyp : ∀ k, ∀ t ∈ Ico (τ₁ k) (τ₂ k), sys.ℓ (φ k) ω t ≤ j ∧ sys.q (φ k) ω t j < 1) :
    ∀ k, ∀ t ∈ Icc (τ₁ k) (τ₂ k), ∀ M : ℝ, (∀ s ∈ Icc 0 D.T, |sys.delta (φ k) ω s j| ≤ M) →
      ∑ i ∈ Finset.Icc 1 j, sys.q (φ k) ω t i - ∑ i ∈ Finset.Icc 1 j, sys.q (φ k) ω (τ₁ k) i ≥
        (∫ s in τ₁ k..t, (D.lam s - D.mu * j)) - 2 * M := by sorry

end UnknownLoads.Refined
