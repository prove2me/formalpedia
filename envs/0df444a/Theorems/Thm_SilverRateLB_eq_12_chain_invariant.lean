-- Prove2me | Theorems.Thm_SilverRateLB_eq_12_chain_invariant
-- name    : SilverRateLB.eq_12_chain_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:44.015205+00:00
-- url     : https://prove2.me/theorems/98614a88-f945-4d12-8e5a-f40131fa1fa0
-- title:
--   (12) — GD on the chain $F$ follows the scaled local iterates
-- statement:
--   Let $\varepsilon,\gamma>0$ with constants $a,c$ of Lemma 2.4, let $H$ be a nonnegative schedule and $T=\{t_1<\dots<t_k\}$ an admissible checkpoint set. For each gap $i\le k$ let $(f_i,\tau_i)$ be a local hard function (the conclusion of Lemma 3.2) for the gap stepsizes $h_{t_{i-1}+1},\dots,h_{t_i-1}$ and $b_i$, and let $F$ be the global hard function (9)–(11). Run gradient descent on $F$ with $H$ from $x_0=e_1$. Then for every $1\le i\le k$, with $m=t_i-t_{i-1}-1$, and every $0\le j\le m+1$: all coordinates of $x_{t_{i-1}+j}$ beyond $i+1$ are zero and
--   $$\bigl(x^{(i)}_{t_{i-1}+j},\,x^{(i+1)}_{t_{i-1}+j}\bigr)=\bigl(\ell_i+D_ix_j,\,D_iy_j\bigr),\tag{12}$$
--   where $(x_j,y_j)$ are the gradient-descent iterates on $f_i/2$ of Lemma 3.2.
--
--   The invariant says that during gap $i$ only the component $\Phi_i$ moves the iterate, so the excess $D_{i+1}$ is passed from one component to the next.
--
--   Differences from the source:
--   - generalization: the functions and thresholds (f_i, τ_i) given by Lemma 3.2 → any pairs satisfying the conclusion of Lemma 3.2 (IsLocalHard); reason: the argument uses only that conclusion; the pairs of Lemma 3.2 satisfy it
--   - encoding: 0 ≤ j ≤ m + 1, m = t_i − t_{i−1} − 1 → j ≤ t_i − t_{i−1}; reason: same range since t_i > t_{i−1}
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §3.1, (12), p. 13

import Mathlib
import Definitions.Def_SilverRateLB_aOf
import Definitions.Def_SilverRateLB_IsLocalHard
import Definitions.Def_SilverRateLB_chainObjective

namespace SilverRateLB

/-- **The chain invariant (12).** Let `ε, γ > 0`, `H` a nonnegative schedule and `T` an admissible
checkpoint set with `k` checkpoints, and for each gap `i ≤ k` let `(f_i, τ_i)` satisfy the
conclusion of Lemma 3.2 for the gap stepsizes `h_{t_{i−1}+1}, …, h_{t_i−1}` and `b_i`. Let `F` be
the objective (11) built with (9), (10), and run GD on `F` with `H` from `e_1`. For every gap
`i`, `m = t_i − t_{i−1} − 1` and `0 ≤ j ≤ m + 1`, all coordinates of `x_{t_{i−1}+j}` beyond
`i + 1` are zero and `(x^{(i)}_{t_{i−1}+j}, x^{(i+1)}_{t_{i−1}+j}) = (ℓ_i + D_i x_j, D_i y_j)`, where
`(x_j, y_j)` are the GD iterates on `f_i/2` of Lemma 3.2.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §3.1, (12), p. 13.

**Formalization Note** Stated for any local data satisfying Lemma 3.2 (`IsLocalHard`), not for a
choice from Lemma 3.2. `x_t` is `gdRun F (H.take t) e_1`; coordinates are 1-based (`coord`);
`j ≤ t_i − t_{i−1}` is `j ≤ m + 1`. -/
theorem eq_12_chain_invariant (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (H : List ℝ) (hH : ∀ h ∈ H, 0 ≤ h)
    (T : Finset ℕ) (hT : IsAdmissible H T) (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ) (τ : ℕ → ℝ)
    (hf : ∀ i ∈ Finset.Icc 1 T.card,
      IsLocalHard (aOf ε γ) (cOf ε γ) (gapList H T i) (ckptStep H T i) (f i) (τ i)) :
    ∀ i ∈ Finset.Icc 1 T.card, ∀ j ≤ tIdx H T i - tIdx H T (i - 1),
      (∀ l, i + 1 < l → coord (gdRun (chainObjective (aOf ε γ) (cOf ε γ) H T f τ)
          (H.take (tIdx H T (i - 1) + j)) (EuclideanSpace.single 0 1)) l = 0) ∧
      coord (gdRun (chainObjective (aOf ε γ) (cOf ε γ) H T f τ)
          (H.take (tIdx H T (i - 1) + j)) (EuclideanSpace.single 0 1)) i =
        chainEll (aOf ε γ) (cOf ε γ) H T τ i +
          chainD (aOf ε γ) (cOf ε γ) H T i * localIter (f i) (gapList H T i) (ckptStep H T i) j 0 ∧
      coord (gdRun (chainObjective (aOf ε γ) (cOf ε γ) H T f τ)
          (H.take (tIdx H T (i - 1) + j)) (EuclideanSpace.single 0 1)) (i + 1) =
        chainD (aOf ε γ) (cOf ε γ) H T i *
          localIter (f i) (gapList H T i) (ckptStep H T i) j 1 := by sorry

end SilverRateLB
