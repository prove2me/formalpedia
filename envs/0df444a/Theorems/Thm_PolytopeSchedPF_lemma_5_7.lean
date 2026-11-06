-- Prove2me | Theorems.Thm_PolytopeSchedPF_lemma_5_7
-- name    : PolytopeSchedPF.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:44.867677+00:00
-- url     : https://prove2.me/theorems/6c79cc37-0a20-45dc-b8b0-3684beaeabd7
-- title:
--   Lemma 5.7 — $\mathrm{OPT}(y\odot\mathbf 1_L)\ge w(L)^2/(2w(A))$ for the Eisenberg–Gale maximizer
-- statement:
--   Let $w>0$, let $A\subseteq J$ be nonempty, and let $y\in\mathcal P$ be a maximizer of $\sum_{j\in A}w_j\log y_j$ over $\mathcal P$. Then for every $L\subseteq A$,
--   $$
--   \mathrm{OPT}(y\odot\mathbf 1_L)\ \ge\ \frac{w(L)^2}{2\,w(A)} .
--   $$
--   In particular, since $\mathrm{OPT}$ is coordinate-wise nondecreasing, $\mathrm{OPT}(y)\ge\mathrm{OPT}(y\odot\mathbf 1_A)\ge\tfrac12w(A)$.
--
--   Applied at every time to the PF rates with $A=L=A(t)$, this says that the weight PF has in the system is at most twice the optimal cost of the work PF processes per unit time.
--
--   Differences from the source:
--   - reading: y ∈ P a maximizer of ∑_{j∈A} w_j log y_j → y ∈ P with y_j > 0 on A, maximal among all y' ∈ P positive on A; reason: with log 0 = −∞ a maximizer is positive on A; Lean's log 0 = 0 would change the comparison set. y may be nonzero off A, as printed
--   - encoding: OPT → opt0 (release dates 0, real infimum); reason: the OPT of §5
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Lemma 5.7, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders

namespace PolytopeSchedPF

/-- **Lemma 5.7** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.3, p.28). For every nonempty `A ⊆ J`, let `y ∈ P` be a maximizer of
`∑_{j∈A} w_j log y_j`. Then, for every `L ⊆ A`, `OPT(y ⊙ 1_L) ≥ w(L)² / (2 w(A))`.
In particular, since OPT is coordinate-wise nondecreasing,
`OPT(y) ≥ OPT(y ⊙ 1_A) ≥ w(A) / 2`.

**Formalization Note** `OPT` is `opt0` (release dates `0`, §5). The maximizer (reading R11) is a
`y ∈ P` with `y_j > 0` on `A` that maximizes `∑_{j∈A} w_j log y'_j` among all `y' ∈ P` positive on
`A` (with `log 0 = −∞` no other vector can be a maximizer); `y` may be nonzero off `A`, as printed. -/
theorem lemma_5_7 {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (A : Finset (Fin n)) (hA : A.Nonempty) (y : Fin n → ℝ) (hyP : y ∈ P.rates)
    (hypos : ∀ j ∈ A, 0 < y j)
    (hymax : ∀ y' ∈ P.rates, (∀ j ∈ A, 0 < y' j) →
      ∑ j ∈ A, w j * Real.log (y' j) ≤ ∑ j ∈ A, w j * Real.log (y j)) :
    (∀ L : Finset (Fin n), L ⊆ A → wsum w L ^ 2 / (2 * wsum w A) ≤ opt0 P w (mask y L)) ∧
    opt0 P w (mask y A) ≤ opt0 P w y ∧ wsum w A / 2 ≤ opt0 P w (mask y A) := by sorry

end PolytopeSchedPF
