-- Prove2me | Theorems.Thm_SONATA_Push_lemma_4_2
-- name    : SONATA.Push.lemma_4_2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T03:20:30.579239+00:00
-- url     : https://prove2.me/theorems/7f672fe1-927f-401b-9324-d1e29ebac017
-- title:
--   Lemma 4.2, pp. 29–30 — weighted consensus errors (81a)–(81b) of push-sum SONATA
-- statement:
--   Consider Problem (P) under Assumptions A and B′, the constants (1) $\mu_i I\preceq\nabla^2 f_i\preceq L_i I$ on $K$ with $L_{\rm mx}=\max_i L_i$, and SONATA (Algorithm 3) under Assumptions C and E, with (15) and a solution $x^\star$. Write $\mathbf x^\nu_{\phi,\perp}=\mathbf x^\nu-\mathbf 1_m\otimes\bar x^\nu_\phi$ and $\mathbf y^\nu_{\phi,\perp}=\mathbf y^\nu-\mathbf 1_m\otimes\bar y^\nu_\phi$ for the weighted consensus errors (75)–(76), $\mathbf d^\nu$ for the stacked directions, and $\phi_{lb}=c_\ell^{2(m-1)B}$ as in (78).
--
--   Then there are network constants $c_0>0$ and $\rho_B\in(0,1)$ (in the source they are the explicit values (79), determined by $m$, $B$ and $c_\ell$) such that for every step size $\alpha\in(0,1]$, every run of Algorithm 3 and every $\nu\ge0$:
--
--   1. $$\|\mathbf x^\nu_{\phi,\perp}\|^2\le 2c_0^2\rho_B^{2\nu}\|\mathbf x^0_{\phi,\perp}\|^2+\frac{2c_0^2\rho_B^2}{1-\rho_B}\sum_{t=0}^{\nu-1}\rho_B^{\nu-1-t}\,\alpha^2\|\mathbf d^t\|^2;\qquad(81a)$$
--   2. $$\|\mathbf y^\nu_{\phi,\perp}\|^2\le 2c_0^2\rho_B^{2\nu}\|\mathbf y^0_{\phi,\perp}\|^2+\frac{2c_0^2\rho_B^2\,m\,L_{\rm mx}^2\,\phi_{lb}^{-2}}{1-\rho_B}\sum_{t=0}^{\nu-1}\rho_B^{\nu-1-t}\big(8\|\mathbf x^t_{\phi,\perp}\|^2+2\alpha^2\|\mathbf d^t\|^2\big).\qquad(81b)$$
--
--   These are the perturbed push-sum consensus estimates over $B$-strongly connected time-varying digraphs; in the proof of Theorem 4.5 they are chained with Propositions 4.1 and 4.3 to obtain the linear rate.
--
--   **Formalization Note** The constants $c_0,\rho_B$ are asserted to exist before the step size and the run are chosen (so they cannot depend on $\alpha$ or on the iterates); their explicit values (79) are not fixed in the statement. The norms are the stacked Euclidean norms (21) (`sqn` is the squared norm), and $\phi_{lb}^{-2}$ appears as division by $\phi_{lb}^2$.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, pp. 29–30, Lemma 4.2, (81a)–(81b); constants (79), p. 29

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- Lemma 4.2 (p. 29–30), (81a)–(81b), with the network constants `c₀ > 0` and `ρ_B ∈ (0,1)`
(given explicitly in (79) in the source) asserted to exist, independently of the step size and of the run. -/
theorem lemma_4_2
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (μi Li : Fin m → ℝ) (h1 : HessBounds K f μi Li) :
    ∃ c0 ρB : ℝ, 0 < c0 ∧ 0 < ρB ∧ ρB < 1 ∧
      ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ x y xh : ℕ → Fin m → SONATA.Undir.E d, ∀ φ : ℕ → Fin m → ℝ, IsRun K f G ft C α x y xh φ →
      ∀ ν : ℕ,
        sqn (wperp (φ ν) (x ν)) ≤
            2 * c0 ^ 2 * ρB ^ (2 * ν) * sqn (wperp (φ 0) (x 0))
              + 2 * c0 ^ 2 * ρB ^ 2 / (1 - ρB) *
                  ∑ t ∈ Finset.range ν, ρB ^ (ν - 1 - t) * (α ^ 2 * sqn (dir x xh t)) ∧
        sqn (wperp (φ ν) (y ν)) ≤
            2 * c0 ^ 2 * ρB ^ (2 * ν) * sqn (wperp (φ 0) (y 0))
              + 2 * c0 ^ 2 * ρB ^ 2 * m * SONATA.Undir.Lmx Li ^ 2 / (phiLb m B cl ^ 2 * (1 - ρB)) *
                  ∑ t ∈ Finset.range ν, ρB ^ (ν - 1 - t) *
                    (8 * sqn (wperp (φ t) (x t)) + 2 * α ^ 2 * sqn (dir x xh t)) := by sorry

end SONATA.Push
