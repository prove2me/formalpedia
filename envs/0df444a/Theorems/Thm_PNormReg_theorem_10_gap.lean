-- Prove2me | Theorems.Thm_PNormReg_theorem_10_gap
-- name    : PNormReg.theorem_10_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:49.437202+00:00
-- url     : https://prove2.me/theorems/2b6ba718-d3b5-4d77-8c40-73fc197d7231
-- title:
--   Proof of Theorem 10, (43), p.41 — Algorithm 6 returns a feasible pair with expected duality gap at most $\epsilon$
-- statement:
--   Let $M\in\mathbb R^{n\times d}$, $c\in\mathbb R^n$, $q\in(1,2]$, $p=q/(q-1)$, $\epsilon\in(0,1)$, with $M_{i:}\ne0$ or $c_i\ne0$ for each $i$, and let
--
--   $$\Lambda\ge\max\{1,\|M\|_{p,2}+\|c\|_p\}.$$
--
--   Then Algorithm 6 returns $(\bar x,\bar y)\in B^d_2\times B^n_q$ and
--
--   $$\mathbb E\Big[\max_{y\in B^n_q}h(\bar x,y)-\min_{x\in B^d_2}h(x,\bar y)\Big]\le\epsilon,$$
--
--   where $h(x,y)=y^\top Mx-c^\top y$ is the original game, and the expectation is over the samples of the algorithm, with the best responses inside it.
--
--   This gives a $\widetilde O(\Lambda^2/((q-1)\epsilon^2))$ iteration count for the $\ell_2$-$\ell_q$ games the reduction produces.
--
--   **Formalization Note** The time clause (44) needs a sparse input format and is carried by Theorem 9.
--
--   Differences from the source:
--   - encoding: Theorem 10 with its time clause (44) → the proof's conclusion (43) with feasibility, cited as Proof of Theorem 10; (44) is not in this item; reason: (44) is a statement about a sparse input format, and the goal carries the cost; this item does not carry the number of Theorem 10 alone
--   - encoding: "(x̄, ȳ) ∈ B^d_2 × B^n_q" → holds for every sequence of samples; reason: it is deterministic: both updates project
--   - reading: the random samples of lines 9 and 12 → two independent samples per round, as a finite recursive sum; reason: the page gives the marginals and does not couple them; the joint law affects later iterates, and the proof's bound holds for every coupling, so independence is one reading of the two "Sample" lines
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Proof of Theorem 10, p.41 (PDF p.42); Theorem 10, (43), p.35; Algorithm 6, p.34

import Mathlib
import Definitions.Def_PNormReg_SMD

open Matrix

namespace PNormReg

/-- **Proof of Theorem 10**, (43), p.41 (PDF p.42); (43) on p.35; Algorithm 6 on p.34.

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

Under (41), for `q ∈ (1, 2]` and `ϵ ∈ (0, 1)`, Algorithm 6 returns `(x̄, ȳ) ∈ B^d_2 × B^n_q` on every
sequence of samples, and `E[max_y h(x̄, y) − min_x h(x, ȳ)] ≤ ϵ`.

**Formalization Note.** `h` is the original game; the estimators use `(M/Λ, c/Λ)` (line 1). The expectation
is over Algorithm 6's own samples, with the best responses inside it. The time clause (44) needs a sparse
input format and is carried by `PNormReg.theorem_9`. -/
theorem theorem_10_gap {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) (q ε Λ : ℝ)
    (hq₁ : 1 < q) (hq₂ : q ≤ 2) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hne : ∀ i, M i ≠ 0 ∨ c i ≠ 0) (hΛ₁ : 1 ≤ Λ)
    (hΛ₂ : rowNormP2 (conjExp q) M + lpNorm (conjExp q) c ≤ Λ) :
    let M' : Matrix (Fin n) (Fin d) ℝ := Λ⁻¹ • M
    let c' : Fin n → ℝ := Λ⁻¹ • c
    let η : ℝ := ε / (27 * Λ)
    let T : ℕ := smdT q ε Λ
    (∀ samples : List (Option (Fin n) × Option (Fin d)), samples.length = T →
      let z := smdAverage T (samples.foldl (smdStep M' c' q η) smdInit)
      l2Norm z.1 ≤ 1 ∧ lpNorm q z.2 ≤ 1) ∧
    smdExpect M' c' q η T (fun s => dualityGap M c q (smdAverage T s)) smdInit ≤ ε := by sorry

end PNormReg
