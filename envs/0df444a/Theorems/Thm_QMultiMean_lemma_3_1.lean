-- Prove2me | Theorems.Thm_QMultiMean_lemma_3_1
-- name    : QMultiMean.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:11.816222+00:00
-- url     : https://prove2.me/theorems/9a6aeadc-c87e-4598-a88c-36688e6a4b65
-- title:
--   Lemma 3.1 — tails of $\langle u,x\rangle$ and $\mathbb E|\langle u,X\rangle|$ for $u$ uniform on the grid (corrected: $x\ne0$, $\mathbb E\|X\|_2>0$)
-- statement:
--   Let $m\ge1$, let $u\sim G$ be uniform on the grid $G$ of side $m$, and let $\alpha>0$.
--
--   1. For every nonzero $x\in\mathbb R^d$,
--   $$\Pr_{u\sim G}\big[\alpha|\langle u,x\rangle|\ge\|x\|_2\big]\le 2e^{-2/\alpha^2}.$$
--   2. For every finite random variable $X$ over $\mathbb R^d$ with $\mathbb E[\|X\|_2]>0$,
--   $$\Pr_{u\sim G}\big[\alpha\,\mathbb E[|\langle u,X\rangle|]\ge\mathbb E[\|X\|_2]\big]\le\frac\alpha2 .$$
--
--   For most grid directions the inner product with $x$ is much smaller than the worst case $\sqrt d\,\|x\|_2$. This is what lets the directional mean be encoded into an amplitude.
--
--   Differences from the source:
--   - correction: for any vector x ∈ ℝ^d and any random variable X → x ≠ 0 in part 1 and E[‖X‖₂] > 0 in part 2; reason: the printed lemma is false in these cases: x = 0, α = 1 gives Pr[0 ≥ 0] = 1 > 2e^{−2}; X ≡ 0, α = 1 gives Pr[0 ≥ 0] = 1 > 1/2; the paper's uses (thresholds 1 in Theorem 3.3 and L₂ > 0 in Proposition 3.2) are unaffected
--   - generalization: m fixed by step 2 of Algorithm 1 → every integer m ≥ 1; reason: the lemma's proof uses only that the grid coordinates are independent, centred and in (−1/2, 1/2); Algorithm 1's m is one value
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.9, Lemma 3.1

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_gridPoint

set_option autoImplicit false

namespace QMultiMean

/-- Lemma 3.1 of Cornelissen, Hamoudi, Jerbi, *Near-Optimal Quantum Algorithms for Multivariate
Mean Estimation*, arXiv:2111.09787v2, p.9, corrected: let `α > 0` and `u ∼ G` uniform on the grid
`G` of p.9. For every nonzero `x ∈ ℝ^d`,
`Pr_{u∼G}[α|⟨u, x⟩| ≥ ‖x‖₂] ≤ 2e^{−2/α²}`, and for every finite random variable `X` over `ℝ^d` with
`E[‖X‖₂] > 0`, `Pr_{u∼G}[αE[|⟨u, X⟩|] ≥ E[‖X‖₂]] ≤ α/2`.

**Formalization Note.** Stated for every grid size `m ≥ 1` (the paper fixes `m` in Algorithm 1). The
hypotheses `x ≠ 0` and `E‖X‖₂ > 0` correct the printed lemma, which is false for `x = 0` and for
`X ≡ 0` (both probabilities are then `1`). The random variable is a probability mass function on
`Fin (N+1)` and a map to `ℝ^d`. -/
theorem lemma_3_1 (d m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) :
    (∀ x : Vec d, x ≠ 0 →
      gridProb d m (fun u => ‖x‖ ≤ α * |inner ℝ (gridPoint m u) x|) ≤ 2 * Real.exp (-2 / α ^ 2)) ∧
    (∀ (N : ℕ) (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d), IsPMF P →
      0 < expect P (fun ω => ‖X ω‖) →
      gridProb d m (fun u => expect P (fun ω => ‖X ω‖) ≤
          α * expect P (fun ω => |inner ℝ (gridPoint m u) (X ω)|)) ≤ α / 2) := by sorry

end QMultiMean
