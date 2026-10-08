-- Prove2me | Theorems.Thm_SkutellaCQP_Preempt_slot_exchange
-- name    : SkutellaCQP.Preempt.slot_exchange
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:13.733336+00:00
-- url     : https://prove2.me/theorems/ae743b33-3e6c-442f-ab91-235669f07c7a
-- title:
--   Proof of Lemma 4.2, p. 22 — exchange inequality: ∑ⱼ xⱼwⱼ ∑_{j′≺ᵢj} x_{j′}p_{ij′} ≤ ∑ⱼ xⱼwⱼ ∑_{j′≺j} x_{j′}p_{ij′} for any total order ≺
-- statement:
--   Fix a machine $i$ of an instance with weights $w_j\ge0$ and processing times $p_{ij}>0$, and let $\prec_i$ be Smith's order on machine $i$: $j\prec_i k$ if $w_j/p_{ij}>w_k/p_{ik}$, or the ratios are equal and $j<k$. Let $x_j\ge0$ be numbers attached to the jobs (in the paper, the fractions $a_{i_kj}$ of one time slot $i_k$), and let $\prec$ be any strict total order on the jobs. Then
--   $$
--   \sum_j x_jw_j\sum_{j'\prec_i j}x_{j'}p_{ij'}\ \le\ \sum_j x_jw_j\sum_{j'\prec j}x_{j'}p_{ij'}.
--   $$
--
--   This is the inequality the proof of Lemma 4.2 reduces the bound (23) to, slot by slot. It is Smith's ratio rule for the "fractional jobs" of processing time $x_jp_{ij}$ and weight $x_jw_j$: ordering them by $\prec_i$ minimizes their total weighted completion time.
--
--   **Formalization Note** The total order $\prec$ is given by a permutation $\pi$ of the jobs, with $j'\prec j$ iff $\pi(j')<\pi(j)$; every strict total order on a finite set arises this way. $\prec_i$ is cross-multiplied ($w_jp_{ik}>w_kp_{ij}$), equal to the ratio form since $p>0$.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), §4, proof of Lemma 4.2, p. 22, last display before the end of the proof

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

namespace SkutellaCQP.Preempt

open Finset

theorem slot_exchange {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (i : Fin m) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (π : Equiv.Perm (Fin n)) :
    ∑ j, x j * w j * ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), x j' * p i j' ≤
      ∑ j, x j * w j * ∑ j' ∈ univ.filter (fun j' => π j' < π j), x j' * p i j' := by sorry

end SkutellaCQP.Preempt
