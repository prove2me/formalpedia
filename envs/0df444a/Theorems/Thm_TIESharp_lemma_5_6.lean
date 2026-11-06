-- Prove2me | Theorems.Thm_TIESharp_lemma_5_6
-- name    : TIESharp.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:54.992197+00:00
-- url     : https://prove2.me/theorems/1595a9e6-6102-43eb-acfa-07880bfbff3b
-- title:
--   Lemma 5.6 — combined improvement on seven machines
-- statement:
--   Let $n=7$, $t$ a nonnegative profile with $T=\mathrm{OPT}(t)=1$, $y$ a slot-rounding law of the Bounded-Square probabilities $q$, $I$ a maximum-load machine chosen in every outcome, $\theta_i=\Pr(I=i)$, and $A^*$ an optimal assignment. Assume $3/4<\|\theta\|_2<1$ and choose a machine $i$ with $\theta_i=\max_\ell\theta_\ell$. If $d_i\le1$, then $\mathbb E[C_{\max}]\le4$. Otherwise, choose a job $j$ with $q_{ij}>0$ and $t_{ij}=d_i$, and let $k=A^*(j)$. Then $k\ne i$, $d_i/2\le t_{kj}\le1$, and
--   $$\mathbb E[C_{\max}]\le\frac12+\frac72\|\theta\|_2+2(1-\|\theta\|_2^2)-(2-d_i)\theta_i(1-\theta_i)-\frac{t_{kj}\big(d_i\theta_i-t_{kj}(\|\theta\|_2+\theta_k)\big)_+^2}{4\big((d_i^2+t_{kj}^2)\|\theta\|_2-d_it_{kj}\theta_i+t_{kj}^2\theta_k\big)}.$$
--   Here $(\cdot)_+=\max\{\cdot,0\}$, and the denominator is positive.
--
--   Differences from the source:
--   - generalization: the distribution of the slot mechanism, with I chosen by fixed tie-breaking → every slot-rounding law (IsBSSlotLaw) and every selection sel attaining the makespan in each outcome; reason: the paper's law and tie-break are instances
--   - encoding: the denominator is positive → (d_i² + t_kj²)‖θ‖₂ − d_i t_kj θ_i + t_kj² θ_k > 0, without the factor 4; reason: equivalent
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 5.6, p.26

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw
import Definitions.Def_TIESharp_dMax
import Definitions.Def_TIESharp_selProb

set_option autoImplicit false

namespace TIESharp

/-- **Lemma 5.6 (Combined improvement)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Lemma 5.6, p.26). Let `n = 7`. Normalize `T = OPT(t) = 1`, assume
`3/4 < ‖θ‖₂ < 1`, and choose a machine `i` with `θ_i = max_ℓ θ_ℓ`. If `d_i ≤ 1`, then
`E[C_max] ≤ 4`. Otherwise, choose a job `j` with `q_ij > 0` and `t_ij = d_i`, and let
`k = A*(j)`. Then `k ≠ i`, `d_i/2 ≤ t_kj ≤ 1`, and
`E[C_max] ≤ 1/2 + (7/2)‖θ‖₂ + 2(1 − ‖θ‖₂²) − (2 − d_i) θ_i (1 − θ_i)
  − t_kj (d_i θ_i − t_kj(‖θ‖₂ + θ_k))₊² / (4((d_i² + t_kj²)‖θ‖₂ − d_i t_kj θ_i + t_kj² θ_k))`.
Here `(·)₊ = max{·, 0}`, and the denominator is positive.

**Formalization Note.** Machines are `Fin 7`. `y` is any slot-rounding law of the Bounded-Square
probabilities (`IsBSSlotLaw`); `sel` picks a maximum-load machine in every outcome (any fixed
tie-breaking rule) and `θ = selProb y sel` are its selection probabilities; `‖θ‖₂ = √(Σ_ℓ θ_ℓ²)`, `A*` any optimal assignment, `E[C_max] = Σ_A y_A C_max(t, A)`. "The
denominator is positive" is a conclusion; it is stated without the factor `4`. -/
theorem lemma_5_6 (m : ℕ) (t : Fin 7 → Fin m → ℝ) (ht : Nonneg t) (hT : opt t = 1)
    (y : (Fin m → Fin 7) → ℝ) (hy : IsBSSlotLaw t y) (sel : (Fin m → Fin 7) → Fin 7)
    (hsel : ∀ A, MatousekLP.Scheduling.load (Matrix.of t) A (sel A)
      = MatousekLP.Scheduling.makespan (Matrix.of t) A)
    (hθ₁ : 3 / 4 < Real.sqrt (∑ l, selProb y sel l ^ 2))
    (hθ₂ : Real.sqrt (∑ l, selProb y sel l ^ 2) < 1)
    (i : Fin 7) (hi : ∀ l, selProb y sel l ≤ selProb y sel i)
    (Astar : Fin m → Fin 7) (hA : MatousekLP.Scheduling.IsOptimalSchedule (Matrix.of t) Astar) :
    (dMax t i ≤ 1 →
      ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 4) ∧
    (1 < dMax t i → ∀ j : Fin m, 0 < bsProb t i j → t i j = dMax t i →
      Astar j ≠ i ∧ dMax t i / 2 ≤ t (Astar j) j ∧ t (Astar j) j ≤ 1 ∧
      0 < (dMax t i ^ 2 + t (Astar j) j ^ 2) * Real.sqrt (∑ l, selProb y sel l ^ 2)
            - dMax t i * t (Astar j) j * selProb y sel i
            + t (Astar j) j ^ 2 * selProb y sel (Astar j) ∧
      ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤
        1 / 2 + 7 / 2 * Real.sqrt (∑ l, selProb y sel l ^ 2)
          + 2 * (1 - ∑ l, selProb y sel l ^ 2)
          - (2 - dMax t i) * selProb y sel i * (1 - selProb y sel i)
          - t (Astar j) j
              * (max (dMax t i * selProb y sel i
                  - t (Astar j) j * (Real.sqrt (∑ l, selProb y sel l ^ 2) + selProb y sel (Astar j))) 0) ^ 2
            / (4 * ((dMax t i ^ 2 + t (Astar j) j ^ 2) * Real.sqrt (∑ l, selProb y sel l ^ 2)
                - dMax t i * t (Astar j) j * selProb y sel i
                + t (Astar j) j ^ 2 * selProb y sel (Astar j)))) := by sorry

end TIESharp
