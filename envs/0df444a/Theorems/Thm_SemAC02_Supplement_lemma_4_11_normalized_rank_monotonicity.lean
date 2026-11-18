-- Prove2me | Theorems.Thm_SemAC02_Supplement_lemma_4_11_normalized_rank_monotonicity
-- name    : SemAC02.Supplement.lemma_4_11_normalized_rank_monotonicity
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-17T19:04:10.541462+00:00
-- url     : https://prove2.me/theorems/1242e022-acdc-4f1c-9c8a-5aed3e0c27b0
-- title:
--   Lemma 4.11: normalised multiplication-image rank is nonincreasing
-- statement:
--   Let $n,h\geq1$, with variables partitioned into $n$ blocks of $h$ variables. Let $\Omega$ consist of Boolean assignments having at most one $1$ in each block, and let $B_{F_0}$ be the algebra of $\mathbb F_2$-valued functions on $\Omega$. Write $B_{F_0}^{\leq k}$ for functions represented by polynomials of total degree at most $k$, and $H_{F_0}(k)=\dim B_{F_0}^{\leq k}$. For $a\in B_{F_0}$ put $r_a(k)=\dim(aB_{F_0}^{\leq k})$.
--
--   For all integers $0\leq j\leq k$,
--
--   $$
--   \frac{r_a(k)}{H_{F_0}(k)}\leq\frac{r_a(j)}{H_{F_0}(j)}.
--   $$
--
--   The ratio is constant for degrees at least $n$. This normalised rank estimate supplies the degree comparison in the proof of the product-approximation Lemma 4.9.
--
--   **Formalization Note** The algebra and its degree filtration use the mission's existing function-space model on $\Omega$. The assertion `Antitone` includes all nonnegative degrees.
-- source:
--   Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, §4.2.1, Lemma 4.11 (Normalised rank monotonicity), printed p.32, https://www.doc.ic.ac.uk/~itzamere/Reslin_Simplification.pdf. Checked against the public manuscript saved in sources/Hard_Instances_Semantic.pdf; its hash differs from the mission-pinned manuscript.

import Mathlib
import Definitions.Def_SemAC02_nDivision

theorem SemAC02.Supplement.lemma_4_11_normalized_rank_monotonicity (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (a : SemAC02.nDivOmega n h → ZMod 2) :
    Antitone (fun k : ℕ =>
      (Module.finrank (ZMod 2) ((SemAC02.BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) a)) : ℝ) /
        (SemAC02.HF0 n h k : ℝ)) := by sorry
