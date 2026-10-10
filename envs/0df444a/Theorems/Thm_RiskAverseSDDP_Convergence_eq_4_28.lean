-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_28
-- name    : RiskAverseSDDP.Convergence.eq_4_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:49:19.829765+00:00
-- url     : https://prove2.me/theorems/44360e05-77af-4bbe-8b0e-d7c1e6a64f9b
-- title:
--   (4.28), proof of Theorem 4.1, p. 13 — under $\mathcal H(t+1)$ the gap at $n$ vanishes along the iterations in $\mathcal S_n$
-- statement:
--   Consider a run of Algorithm 1 for the problem (3.9), under the standing assumptions and Assumption (H2). Let $t\in\{2,\dots,T\}$ and let $n$ be a node of stage $t-1$. Suppose that for every child $m$ of $n$
--   $$
--   \lim_{k\to+\infty}\mathcal Q_{t+1}(x^k_{[m]})-\mathcal Q^k_{t+1}(x^k_{[m]})=0.\tag{4.27}
--   $$
--   Then
--   $$
--   \lim_{k\to+\infty,\ k\in\mathcal S_n}\mathcal Q_t(x^k_{[n]})-\mathcal Q^k_t(x^k_{[n]})=0,\tag{4.28}
--   $$
--   where $\mathcal S_n=\{k\ge1:\ n^k_{t-1}=n\}$.
--
--   This is the deterministic half of the induction step $\mathcal H(t+1)\Rightarrow\mathcal H(t)$ in the proof of Theorem 4.1.
--
--   **Formalization Note** Limits are in $\mathbb R\cup\{\pm\infty\}$ (convergence to $0$ forces the differences to be eventually finite). The limit along $\mathcal S_n$ is a limit along the filter `atTop ⊓ 𝓟 𝒮_n`; if $\mathcal S_n$ is finite the claim is vacuous, which is the meaning of a limit along a finite index set (under (H3), $\mathcal S_n$ is almost surely infinite). The step from (4.27) to the corresponding limit with $\mathcal Q^{k-1}_{t+1}$ is Lemma A.1 of Girardeau–Leclère–Philpott.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 13, (4.27)–(4.28) in the proof of Theorem 4.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
open Filter Topology

namespace RiskAverseSDDP.Convergence

theorem eq_4_28 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) (s : ℕ) (hs : s + 2 ≤ T) (ν : Fin s → Fin M)
    (h427 : ∀ j : Fin M, Tendsto (fun k =>
      D.Q (s + 2) (r.hist k (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)) -
        r.Qm k (s + 2) (r.hist k (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j))) atTop (𝓝 0)) :
    Tendsto (fun k => D.Q (s + 1) (r.hist k s ν) - r.Qm k (s + 1) (r.hist k s ν))
      (atTop ⊓ 𝓟 (iterSet ys s ν)) (𝓝 0) := by sorry

end RiskAverseSDDP.Convergence
