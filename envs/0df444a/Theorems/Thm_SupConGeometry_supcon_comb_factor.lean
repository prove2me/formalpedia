-- Prove2me | Theorems.Thm_SupConGeometry_supcon_comb_factor
-- name    : SupConGeometry.supcon_comb_factor
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:11:43.634339+00:00
-- url     : https://prove2.me/theorems/3ce13cc0-0ae3-43c6-bac0-37fa300bfda7
-- title:
--   Lemma 7 (as proved): value of the combinatorial factor $K_{n,m}(y,l)$
-- statement:
--   Let $b\ge3$, $l\in\{1,\dots,b-1\}$, $Y\in[K]^N$ and $y\in[K]$, and let $n,m\in[N]$ with $y_n=y$ and $y_m\neq y$. Then the combinatorial factor of Lemma 5 equals
--
--   $$K_{n,m}(y,l)=\frac{|\mathcal B_{y,l}|}{m_Y(y)\,\big(N-m_Y(y)\big)}.$$
--
--   It is the counting step that turns the sum of repulsion terms over batches into a weighted sum over pairs of indices.
--
--   **Formalization Note** The paper states the identity "for every $n,m\in[N]$". Its proof, and its only use (Lemma 9), take $y_n=y$ and $y_m\neq y$. For other pairs the factor is $0$, because $m_{B_y}(n)=0$ or $m_{B_y^C}(m)=0$, and the printed identity fails. The statement is restricted accordingly. No balance assumption is needed.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Supplementary S1.3, Lemma 7, eq. (82), p. 22 (factor defined in Lemma 5, eq. (61), p. 20)

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem supcon_comb_factor {N K b : ℕ} (hb : 3 ≤ b) (Y : Fin N → Fin K) (y : Fin K) (l : ℕ)
    (hl : 1 ≤ l) (hlb : l < b) (n m : Fin N) (hn : Y n = y) (hm : Y m ≠ y) :
    combFactor Y b y l n m =
      ((batchesWithCount Y b y l).card : ℝ) /
        ((labelCount Y y : ℝ) * ((N : ℝ) - (labelCount Y y : ℝ))) := by sorry

end SupConGeometry
