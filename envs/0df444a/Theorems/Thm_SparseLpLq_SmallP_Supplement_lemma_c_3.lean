-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_Supplement_lemma_c_3
-- name    : SparseLpLq.SmallP.Supplement.lemma_c_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:14:41.73181+00:00
-- url     : https://prove2.me/theorems/04adf65d-3c51-447b-b126-2ebe42046fe1
-- title:
--   Lemma C.3 — a constant c > 0 with dist(x, FEA(A,b,σ,1)) ≤ c(‖Ax − b‖₁ − σ)₊ for every x
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, and the blanket assumptions of the paper (p. 1) hold for $q=1$: $\sigma\ge 0$, $\mathrm{FEA}(A,b,\sigma,1)=\{x:\|Ax-b\|_1\le\sigma\}\neq\emptyset$ and $\|b\|_1>\sigma$.
--
--   There exists a constant $c>0$ such that for every $x\in\mathbb R^n$,
--   $$\mathrm{dist}\big(x,\mathrm{FEA}(A,b,\sigma,1)\big)\ \le\ c\,\big(\|Ax-b\|_1-\sigma\big)_+ ,$$
--   where $\mathrm{dist}$ is the Euclidean distance and $(t)_+=\max\{t,0\}$.
--
--   This is an error bound: the constraint violation controls the distance to the feasible set. It is the key estimate behind the exact penalty results, Theorems C.1–C.3; Theorem C.3 uses its constant $c$ explicitly.
--
--   **Formalization Note** The distance is `Metric.infDist` in `EuclideanSpace ℝ (Fin n)`.
--
--   Differences from the source:
--   - reading: dist(x, FEA(A,b,σ,1)), norm not named → Euclidean distance (Metric.infDist in EuclideanSpace ℝ (Fin n)); reason: the paper's balls ℬ(y;δ) (p. 4) and the proof of Theorem C.3 (p. 27, ‖·‖ with n^{1−p/2}) use the Euclidean norm; the existence of c holds for any norm, so the reading only fixes which c Theorem C.3 refers to
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 25, Lemma C.3; proof p. 25 (via Lemma C.2, p. 24)

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty

open scoped ENNReal Matrix Topology

namespace SparseLpLq.SmallP.Supplement
open SparseLpLq.SmallP
theorem lemma_c_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ,
      distFEA A b σ x ≤ c * max (qNorm 1 (A *ᵥ x - b) - σ) 0 := by sorry
end SparseLpLq.SmallP.Supplement
