-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_5_15
-- name    : RobustCorrClust.Main.lemma_5_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:41:30.450954+00:00
-- url     : https://prove2.me/theorems/93785fc2-4362-482c-8ecb-ff6f1d24c8ce
-- title:
--   Lemma 5.15 — projected gradient descent with ν³-accurate gradients: ȳ ∈ B and φ(ȳ) − φ(y⋆) ≤ ν²/2
-- statement:
--   Let $C$ be a weighted adjacency matrix, $\xi\in(0,1]$, and $\nu=\xi/(100nR^2)$, $\eta=\nu^3$, $T=\lceil\nu^{-6}\rceil$ the parameters of Algorithm 1. Run Algorithm 1 with vectors $x^{t,u}$ in line 4 (iteration $t$, vertex $u$) such that
--   $$\big|x^{t,u}_u-(M(y_t)^+)_{uu}\big|\le\nu^3\qquad\text{for every }1\le t\le T\text{ and every }u .$$
--   Then the output $\bar y=\tfrac1T\sum_{t=1}^Ty_t$ lies in $B$ and
--   $$\varphi(\bar y)-\varphi(y^\star)\le\nu^2/2,$$
--   where $y^\star$ minimizes $\varphi$ over $\mathbb R^n$.
--
--   Differences from the source:
--   - generalization: $C$ the weighted adjacency matrix of the rescaled sparsifier $\tilde H$ ("here and throughout Part B", p. 21) → $C$ any weighted adjacency matrix (symmetric, nonnegative, zero diagonal), the input class of Theorem 3; reason: Theorem 3 is stated for this general $C$ (p. 21) and the lemma is part of its proof; the paper's $\tilde H$ is such a matrix.
--   - generalization: the vector $x$ computed by Polynomial-Approx (Algorithm 3) → any vectors $x^{t,u}$ (each may depend on the current iterate) meeting the accuracy hypothesis at the current iterate $y_t$; reason: the lemma's hypothesis is only this accuracy, and Algorithm 3's output is such a family.
--   - reading: "the vector $x$ computed in line 5" → the vector obtained in line 4; reason: typo, $x$ is computed in line 4 and used in line 5 (Lemma 5.16 says line 4).
--   - encoding: $\varphi(\bar y)-\varphi(y^\star)\le\nu^2/2$ → $\varphi(\bar y)-\varphi(z)\le\nu^2/2$ for every $z$; reason: equivalent, a minimizer exists (Lemma 5.10).
--   - encoding: $n=0$ → included without hypothesis; reason: the paper's $\nu$ is undefined at $n=0$, and the Lean statement is trivially true there (one point in $\mathbb R^0$).
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 33, Lemma 5.15

import Mathlib
import Definitions.Def_RobustCorrClust_Main_NCMDual

namespace RobustCorrClust.Main

/-- Lemma 5.15 (p. 33): if at every iteration `t ≤ T` and for every vertex `u` the vector `x`
obtained in line 4 of Algorithm 1 satisfies `|x_u − (M(y_t)⁺)_uu| ≤ ν³`, then the output `ȳ`
lies in `B` and `φ(ȳ) − φ(y⋆) ≤ ν²/2` (`y⋆` a minimizer of `φ`, i.e. `φ(ȳ) − φ(z) ≤ ν²/2`
for every `z ∈ ℝⁿ`). The oracle `x` is arbitrary subject to this accuracy. -/
theorem lemma_5_15 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsWeightedGraph C)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1) (x : ℕ → Fin n → Fin n → ℝ)
    (hx : ∀ t, 1 ≤ t → t ≤ iterPar C ξ → ∀ u,
      |x t u u - posPart (Mmat C (pgdY C ξ x t)) u u| ≤ nuPar C ξ ^ 3) :
    InBox C (pgdOut C ξ x) ∧
      ∀ z : Fin n → ℝ, phi C (pgdOut C ξ x) - phi C z ≤ nuPar C ξ ^ 2 / 2 := by sorry

end RobustCorrClust.Main
