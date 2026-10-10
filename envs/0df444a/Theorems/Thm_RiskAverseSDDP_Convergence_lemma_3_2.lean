-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_lemma_3_2
-- name    : RiskAverseSDDP.Convergence.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:48:53.524588+00:00
-- url     : https://prove2.me/theorems/89a3adad-888d-4bd3-a84c-8dd4465b2035
-- title:
--   Lemma 3.2 — the cuts of Algorithm 1 are valid, their coefficients are bounded, and $\mathcal Q^k_t$ is convex Lipschitz on $[\mathcal X_1\times\dots\times\mathcal X_{t-1}]^\varepsilon$
-- statement:
--   Consider a run of Algorithm 1 for the problem (3.9), under the standing assumptions and Assumption (H2) with constant $\varepsilon>0$, and write $F_t=[\mathcal X_1\times\dots\times\mathcal X_{t-1}]^\varepsilon$. Then for $t=2,\dots,T+1$:
--   1. **(a)** for all $k\ge1$, $\mathcal Q^k_t$ is convex and $\mathcal Q^k_t\le\mathcal Q_t$ on $F_t$;
--   2. **(b)** the sequences $(\theta^k_t)_{k\ge T-t+1}$, $(\beta^k_t)_{k\ge T-t+1}$ and $(\pi_{k,m})_{k\ge T-t+1}$ are bounded: the $\theta^k_t$ are finite and there is a single $B$ with $|\theta^k_t|\le B$, $\|\beta^k_t\|\le B$ and $\|\pi_{k,m}\|\le B$ for all $k\ge T-t+1$ and all children $m$ of the sampled node $n^k_{t-1}$;
--   3. **(c)** for $k\ge T-t+1$, $\mathcal Q^k_t$ is finite, convex and Lipschitz continuous on $F_t$.
--
--   This lemma is the "valid cuts" and regularity half of the convergence analysis: the cutting-plane models stay below the recourse functions and become uniformly regular after the first $T-t+1$ iterations.
--
--   **Formalization Note** The paper says "almost surely"; the statement holds for every run (it involves no probability), and is stated per run. Part (b) is stated for $t\le T$: for $t=T+1$ the cuts are identically zero. Convexity in (a) is convexity of the extended-real function $\mathcal Q^k_t$ on $\mathbb R^{n(t-1)}$; in (c) it is convexity of its real values on $F_t$. Lean index: `Qm k h` is $\mathcal Q^k_{h+1}$ ($h=t-1$), `θ k s`, `β k s`, `π k s j` are $\theta^k_{s+2}$, $\beta^k_{s+2}$, $\pi_{k,m}$ ($s=t-2$); $k\ge T-t+1$ is written `T ≤ k + h` resp. `T ≤ k + s + 1`.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 10, Lemma 3.2 (with (3.21), (3.22) on p. 11)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run

namespace RiskAverseSDDP.Convergence

theorem lemma_3_2 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    (∀ h, 1 ≤ h → h ≤ T → ∀ k, 1 ≤ k →
      EConvex (r.Qm k h) ∧ ∀ x ∈ Metric.cthickening ε (D.prodSet h), r.Qm k h x ≤ D.Q h x) ∧
    (∀ s, s + 2 ≤ T → ∃ B : ℝ, ∀ k, T ≤ k + s + 1 →
      (r.θ k s ≠ ⊥ ∧ r.θ k s ≠ ⊤ ∧ |(r.θ k s).toReal| ≤ B) ∧ ‖r.β k s‖ ≤ B ∧
      ∀ j, ‖r.π k s j‖ ≤ B) ∧
    (∀ h, 1 ≤ h → h ≤ T → ∀ k, T ≤ k + h →
      (∀ x ∈ Metric.cthickening ε (D.prodSet h), r.Qm k h x ≠ ⊥ ∧ r.Qm k h x ≠ ⊤) ∧
      ConvexOn ℝ (Metric.cthickening ε (D.prodSet h)) (fun x => (r.Qm k h x).toReal) ∧
      ∃ L : ℝ, ∀ x ∈ Metric.cthickening ε (D.prodSet h), ∀ y ∈ Metric.cthickening ε (D.prodSet h),
        |(r.Qm k h x).toReal - (r.Qm k h y).toReal| ≤ L * ‖x - y‖) := by sorry

end RiskAverseSDDP.Convergence
