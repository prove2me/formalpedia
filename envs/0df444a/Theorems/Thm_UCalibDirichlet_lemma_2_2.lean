-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_2_2
-- name    : UCalibDirichlet.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:25:44.678274+00:00
-- url     : https://prove2.me/theorems/9b98c265-7563-4236-a93c-c78e525e4761
-- title:
--   Lemma 2.2 — multinomial scale comparison $L_F(n)\le 78L_F(m)$
-- statement:
--   Let $F:\Delta_K\to\mathbb R$ be convex (and finite). Then:
--   1. for all integers $1\le n\le m$, $L_F(n)\le 78\,L_F(m)$;
--   2. consequently, for $T\ge K$,
--   $$\sup_{K\le n\le K+T}L_F(n)\le 78\,L_F(T).$$
--
--   The comparison lets every complexity term $L_F(n_t)$ with $n_t=\|a_t\|_1\in[K,K+T)$ arising in the analysis of Algorithm 1 be replaced by $L_F(T)$.
--
--   Differences from the source:
--   - encoding: sup over integers K ≤ n ≤ K + T → ∀ n : ℕ, K ≤ n → n ≤ K + T → L_F(n) ≤ 78 L_F(T); reason: a supremum over a finite set is at most a bound iff every element is
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 2.2, display (19), p.13

import Mathlib
import Definitions.Def_UCalibDirichlet_LF

namespace UCalibDirichlet

/-- **Lemma 2.2 (multinomial scale comparison).** Frongillo, Luo, Mehta & Schneider (manuscript,
STOC 2027 submission), Lemma 2.2, display (19), p.13: "For integers `1 ≤ n ≤ m` and finite convex
`F`, it holds that `L_F(n) ≤ 78 L_F(m)`. Consequently, for `T ≥ K`,
`sup_{K≤n≤K+T} L_F(n) ≤ 78 L_F(T)`. (19)"

Both clauses are stated: (a) `L_F(n) ≤ 78 L_F(m)` for `1 ≤ n ≤ m`; (b) for `T ≥ K`, every integer
`n` with `K ≤ n ≤ K + T` has `L_F(n) ≤ 78 L_F(T)` (the supremum over finitely many `n`).

**Formalization Note.** "Finite convex `F`" is a real-valued `F` convex on `Δ_K`. The constant 78
is the paper's (proof on p.28: `36n/(n − 1/2) + 6n/m ≤ 78`). -/
theorem lemma_2_2 {K : ℕ} (F : (Fin K → ℝ) → ℝ) (hF : ConvexOn ℝ (stdSimplex ℝ (Fin K)) F) :
    (∀ n m : ℕ, 1 ≤ n → n ≤ m → LF F n ≤ 78 * LF F m) ∧
      ∀ T : ℕ, K ≤ T → ∀ n : ℕ, K ≤ n → n ≤ K + T → LF F n ≤ 78 * LF F T := by sorry

end UCalibDirichlet
