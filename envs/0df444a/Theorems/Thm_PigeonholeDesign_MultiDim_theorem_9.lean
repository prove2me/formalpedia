-- Prove2me | Theorems.Thm_PigeonholeDesign_MultiDim_theorem_9
-- name    : PigeonholeDesign.MultiDim.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:36:23.477969+00:00
-- url     : https://prove2.me/theorems/29679fbd-3a92-40c8-8c20-5ed53f949c2d
-- title:
--   Theorem 9 — with p ≥ 2 continuous covariates the pigeonhole design has expected discrepancy O(T^{1−φ} + T^{(p−1)φ}), times (log T)^{3/2} at p = 2
-- statement:
--   Consider $T$ subjects (with $T$ even) arriving in a fixed order. Each subject has $q$ discrete covariates, the $i$-th taking values in a finite set $S_i\subseteq[0,1]$, and $p\ge2$ continuous covariates in $[0,1]$. Distances are Euclidean in $\mathbb R^{q+p}$.
--
--   Fix $\varphi\in(0,1)$ and $c>1$. Run the pigeonhole design with the pigeonholes
--   $$\mathcal P(\mathcal S)=S_1\times\cdots\times S_q\times\Big\{\big[0,c^{1/p}T^{-\varphi}\big),\big[c^{1/p}T^{-\varphi},2c^{1/p}T^{-\varphi}\big),\dots,\big[1-c^{1/p}T^{-\varphi},1\big]\Big\}^p .$$
--   Its expected discrepancy (the minimum-weight perfect matching between the control and the treated group, averaged over the design's fair coins) satisfies, uniformly over all arrival sequences,
--   $$\mathbb E[d_{A,B}]=\begin{cases}O\Big(T^{1-\varphi}+T^{(p-1)\varphi}(\log T)^{3/2}\Big), & p=2,\\[4pt] O\Big(T^{1-\varphi}+T^{(p-1)\varphi}\Big), & p\ge3 .\end{cases}$$
--   That is, there are $C>0$ and $T_0$, depending only on $p,q,S_1,\dots,S_q,\varphi,c$, such that the bound holds with constant $C$ for every even $T\ge T_0$ and every admissible arrival sequence.
--
--   At $\varphi=1/p$ the bound is $O(T^{(p-1)/p})$ for $p\ge3$, which is the order of the discrepancy of the clairvoyant matched-pair design (Theorem 7). An online design that sees each subject only on arrival therefore matches the offline benchmark.
--
--   **Formalization Note** The printed cell edge $c^{1/p}T^{-\varphi}$ gives a partition only when $c^{-1/p}T^{\varphi}$ is an integer; the formalization uses $m=\lceil c^{-1/p}T^{\varphi}\rceil$ cells of edge $1/m\le c^{1/p}T^{-\varphi}$ per axis, the last cell closed. The two bullets are one statement with a case split on $p=2$. $\log$ is natural. The expectation is the average over all $2^T$ coin vectors, not the discrepancy of a single run; $C$ and $T_0$ do not depend on $T$ or $x$. The supports $S_i\subseteq[0,1]$ are the paper's normalisation of the covariate space to $[0,1]^{p+q}$.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 26, Theorem 9

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting

namespace PigeonholeDesign.MultiDim

theorem theorem_9 (p q : ℕ) (hp : 2 ≤ p) (S : Fin q → Finset ℝ)
    (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1) (φ c : ℝ) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hc : 1 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → Cov q p, Admissible S x →
        PigeonholeDesign.Upper.phdExp (gridHole (cellsPerAxis p c φ T)) x
          ≤ C * ((T : ℝ) ^ ((1 : ℝ) - φ) + (T : ℝ) ^ (((p : ℝ) - 1) * φ) *
                  (if p = 2 then Real.log T ^ ((3 : ℝ) / 2) else 1)) := by sorry

end PigeonholeDesign.MultiDim
