-- Prove2me | Theorems.Thm_SupConGeometry_supcon_outer_bound
-- name    : SupConGeometry.supcon_outer_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:11:14.387515+00:00
-- url     : https://prove2.me/theorems/65f51ba6-76f7-4fe3-9038-52b17d897727
-- title:
--   Lemma 3: outer lower bound on the supervised contrastive loss
-- statement:
--   Throughout, $h,N,K\in\mathbb N$ with $K\le h+1$, the batch size is $b\ge3$, $\rho>0$, and every $z_n$ lies on the sphere $\mathbb S^{h-1}_\rho=\{z\in\mathbb R^h:\|z\|=\rho\}$ (standing assumptions of Supplementary S1).
--
--   For every labelling $Y\in[K]^N$ and every $Z$ on the sphere,
--
--   $$\mathcal L_{SC}(Z;Y)\ \ge\ \sum_{l=2}^b l\,M_l\log\Big(l-1+(b-l)\exp\Big(\frac1{M_l}\sum_{y}\sum_{B\in\mathcal B_{y,l}}S(Z;Y,B,y)\Big)\Big),$$
--
--   with equality if and only if
--   1. (A1) there is $\alpha$ with $\langle z_n,z_m\rangle=\alpha$ whenever $y_n=y_m$ (including $n=m$), and
--   2. (A2) there is $\beta$ with $\langle z_n,z_m\rangle=\beta$ whenever $y_n\neq y_m$.
--
--   It combines Lemma 1 with Jensen's inequality for $x\mapsto\log(l-1+(b-l)e^x)$ over all triples $(y,B,i)$ with $B\in\mathcal B_{y,l}$, $i\in B_y$.
--
--   **Formalization Note** A term with $M_l=0$ is read as $0$ (Lean's $1/0=0$ makes its factor $l\,M_l=0$). The paper leaves this expression undefined. It occurs only when $N=0$, or for $l<b$ when $Y$ uses a single label.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Supplementary S1.3, Lemma 3, eq. (48), p. 17; standing assumptions of Supplementary S1, p. 12

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem supcon_outer_bound {N K h b : ℕ} (hKh : K ≤ h + 1) (hb : 3 ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ = ρ) (Y : Fin N → Fin K) :
    (∑ l ∈ Icc 2 b, (l : ℝ) * (batchCountTotal Y b l : ℝ) *
        Real.log ((l : ℝ) - 1 + ((b : ℝ) - l) *
          Real.exp ((1 / (batchCountTotal Y b l : ℝ)) *
            ∑ y, ∑ B ∈ batchesWithCount Y b y l, sAux Z Y B y))) ≤ scLoss Z Y b ∧
    (scLoss Z Y b =
        ∑ l ∈ Icc 2 b, (l : ℝ) * (batchCountTotal Y b l : ℝ) *
          Real.log ((l : ℝ) - 1 + ((b : ℝ) - l) *
            Real.exp ((1 / (batchCountTotal Y b l : ℝ)) *
              ∑ y, ∑ B ∈ batchesWithCount Y b y l, sAux Z Y B y)) ↔
      (∃ α : ℝ, ∀ n m : Fin N, Y n = Y m → inner ℝ (Z n) (Z m) = α) ∧
      (∃ β : ℝ, ∀ n m : Fin N, Y n ≠ Y m → inner ℝ (Z n) (Z m) = β)) := by sorry

end SupConGeometry
