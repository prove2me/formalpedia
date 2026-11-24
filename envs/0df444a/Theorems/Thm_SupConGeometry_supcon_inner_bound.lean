-- Prove2me | Theorems.Thm_SupConGeometry_supcon_inner_bound
-- name    : SupConGeometry.supcon_inner_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:12:34.630924+00:00
-- url     : https://prove2.me/theorems/9bf37d12-9982-433d-a328-9e92fe7f1d9d
-- title:
--   Lemma 10 (as proved): lower bound on the averaged exponent
-- statement:
--   Throughout, $h,N,K\in\mathbb N$ with $K\le h+1$, the batch size is $b\ge3$, $\rho>0$, and every $z_n$ lies on the sphere $\mathbb S^{h-1}_\rho=\{z\in\mathbb R^h:\|z\|=\rho\}$ (standing assumptions of Supplementary S1). In addition, $K\ge2$, $N\ge1$ and $Y$ is balanced.
--
--   For every $l\in\{2,\dots,b-1\}$,
--
--   $$\frac1{M_l}\sum_y\sum_{B\in\mathcal B_{y,l}}S(Z;Y,B,y)\ \ge\ -\frac{K}{K-1}\,\rho^2,$$
--
--   with equality if and only if
--   1. (A3) $y_n=y_m$ implies $z_n=z_m$, and
--   2. (A4) $\sum_{n\in[N]}z_n=0$.
--
--   It bounds the exponent in Lemma 3 using the attraction bound (Lemma 4) and the repulsion bound (Lemmas 5-9).
--
--   **Formalization Note** The printed right-hand side is $+\frac{K}{K-1}\rho^2$. The proof derives $-|\mathcal Y||\mathcal B_{y,l}|\rho^2\frac{K}{K-1}=-M_l\frac{K}{K-1}\rho^2$, and Lemma 11 uses the negative sign. The printed version is false: at the simplex configuration the left side equals $-\frac{K}{K-1}\rho^2$. The statement is the one the proof establishes. $N\ge1$ is needed: for $N=0$ the left side is $0$ (with Lean's $1/0=0$) and the equality claim fails.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Supplementary S1.3, Lemma 10, eq. (108), p. 25 (sign as derived in its proof, p. 25); standing assumptions of Supplementary S1, p. 12

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem supcon_inner_bound {N K h b : ℕ} (hK : 2 ≤ K) (hKh : K ≤ h + 1) (hb : 3 ≤ b)
    (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ = ρ)
    (Y : Fin N → Fin K) (hY : IsBalanced Y) (l : ℕ) (hl : 2 ≤ l) (hlb : l < b) :
    -((K : ℝ) / ((K : ℝ) - 1)) * ρ ^ 2 ≤
      (1 / (batchCountTotal Y b l : ℝ)) * ∑ y, ∑ B ∈ batchesWithCount Y b y l, sAux Z Y B y ∧
    ((1 / (batchCountTotal Y b l : ℝ)) * ∑ y, ∑ B ∈ batchesWithCount Y b y l, sAux Z Y B y =
        -((K : ℝ) / ((K : ℝ) - 1)) * ρ ^ 2 ↔
      (∀ n m : Fin N, Y n = Y m → Z n = Z m) ∧ ∑ n, Z n = 0) := by sorry

end SupConGeometry
