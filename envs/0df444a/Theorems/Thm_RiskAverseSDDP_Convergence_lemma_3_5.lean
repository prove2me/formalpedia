-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_lemma_3_5
-- name    : RiskAverseSDDP.Convergence.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:50:16.209014+00:00
-- url     : https://prove2.me/theorems/d23ba9d2-3123-48fa-b373-a32ca4168ee5
-- title:
--   Lemma 3.5 — for $k\ge T-t+1$ the approximations $\mathcal Q^k_t$ are $L$-Lipschitz with an explicit $L$
-- statement:
--   Consider a run of Algorithm 1 for the problem (3.9), under the standing assumptions and Assumption (H2) with constant $\varepsilon>0$. Let
--   $$
--   L=\frac2\varepsilon\,\max_{t=2,\dots,T}\Big(\sup_{x_{1:t-1}\in[\mathcal X_1\times\dots\times\mathcal X_{t-1}]^{\varepsilon/2}}\mathcal Q_t(x_{1:t-1})\;-\;\min_{x_{1:t-1}\in\mathcal X_1\times\dots\times\mathcal X_{t-1}}\mathcal Q^{T-t+1}_t(x_{1:t-1})\Big).
--   $$
--   Then $L$ is a (finite) real number, and for $t=2,\dots,T$ and $k\ge T-t+1$ the function $\mathcal Q^k_t$ is finite on $\mathbb R^{n(t-1)}$ and $L$-Lipschitz:
--   $$
--   |\mathcal Q^k_t(x)-\mathcal Q^k_t(y)|\le L\,\|x-y\|\qquad\text{for all }x,y\in\mathbb R^{n(t-1)}.
--   $$
--
--   The constant does not depend on $t$ or $k$; this uniform Lipschitz property is what allows the passage from $\mathcal Q^k_{t+1}$ to $\mathcal Q^{k-1}_{t+1}$ in the proof of Theorem 4.1.
--
--   **Formalization Note** $L$ depends on the run through $\mathcal Q^{T-t+1}_t$. The supremum and the minimum are computed in $\mathbb R\cup\{\pm\infty\}$ (the minimum as an infimum), and finiteness of $L$ is part of the conclusion. "$L$-Lipschitz" is global on $\mathbb R^{n(t-1)}$, as for a maximum of finitely many affine functions. In Lean, $t=h+1$: `Qm k h` is $\mathcal Q^k_t$ and $k\ge T-t+1$ is `T ≤ k + h`.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 12, Lemma 3.5

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run

namespace RiskAverseSDDP.Convergence

theorem lemma_3_5 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    let L : EReal := ((2 / ε : ℝ) : EReal) *
      ⨆ h', ⨆ (_ : 1 ≤ h' ∧ h' + 1 ≤ T),
        ((⨆ x ∈ Metric.cthickening (ε / 2) (D.prodSet h'), D.Q h' x) -
          ⨅ x ∈ D.prodSet h', r.Qm (T - h') h' x)
    ∀ h, 1 ≤ h → h + 1 ≤ T → ∀ k, T ≤ k + h →
      L ≠ ⊥ ∧ L ≠ ⊤ ∧
      ∀ x y : Hist n h, r.Qm k h x ≠ ⊥ ∧ r.Qm k h x ≠ ⊤ ∧
        |(r.Qm k h x).toReal - (r.Qm k h y).toReal| ≤ L.toReal * ‖x - y‖ := by sorry

end RiskAverseSDDP.Convergence
