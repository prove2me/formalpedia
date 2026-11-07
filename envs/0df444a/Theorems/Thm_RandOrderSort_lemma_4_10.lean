-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_10
-- name    : RandOrderSort.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:00.001579+00:00
-- url     : https://prove2.me/theorems/88f92d02-d703-432c-8b8c-a446c749652b
-- title:
--   Lemma 4.10 — uniform reverse moment
-- statement:
--   Let $n\ge 8192$ and set
--   $$\theta_g=\frac1{32768},\qquad M_g=e^{D_g/16384}\Bigl(1+\frac{A_ge^{-32}}{1-e^{-1/2}}\Bigr).$$
--   For every fixed prefix set $P_L$ and every strict cut induced in $P_L$,
--   $$\mathbb E\Bigl[\exp\Bigl(\theta_g\sum_{j=0}^{L-1}G_j\Bigr)\Bigm|P_L\Bigr]\le M_g^L.$$
--   For every deterministic value cut $q$, this conditional inequality holds almost surely in the i.i.d. experiment.
--
--   This combines the growing-phase witnesses across all phases, one factor $M_g$ per phase.
--
--   **Formalization Note** In the first sentence the fixed set is $\{0,\dots,m-1\}$ up to order isomorphism and its arrival order is a uniform permutation. In the second, the conditioning is on $\sigma(P_L)$, and the integrand is stated to be integrable.
--
--   Differences from the source:
--   - encoding: a fixed prefix set P_L with its arrival order random → the population {0, …, m−1} with a uniform permutation τ of arrivals; reason: only the order of P_L matters; the bound for each fixed set is the conditional statement
--   - encoding: conditioning on P_L in the i.i.d. experiment → `condExp` given `HL n`, the σ-algebra of the prefix's order statistics, with `HL n ≤ pi` and integrability stated; reason: the order statistics and the unordered set determine each other
--   - generalization: a deterministic value cut q, with q ∈ (0, 1) standing in §4.2 (p.23) → every real q; reason: a q outside (0, 1) induces an outer cut of P_L almost surely, which the first sentence covers; the Lean specializes to the page's q ∈ (0, 1)
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.10, p.31, displays (41), (42)

import Mathlib
import Definitions.Def_RandOrderSort_Gj
import Definitions.Def_RandOrderSort_iidUnif
open MeasureTheory

namespace RandOrderSort

/-- **Lemma 4.10 (Uniform reverse moment)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.31: "Set θ_g = 1/32768,
M_g = e^{D_g/16384}(1 + A_g e^{−32}/(1 − e^{−1/2})). (41) For every fixed prefix set P_L and every strict
cut induced in P_L, E[exp(θ_g ∑_{j=0}^{L−1} G_j) | P_L] ≤ M_g^L. (42) For every deterministic value
cut q, this conditional inequality holds almost surely in the i.i.d. experiment."

**Formalization Note.** For `n ≥ 8192`. First sentence: a fixed strictly
ordered `P_L` of `m` keys is, up to order isomorphism, `{0, …, m − 1}`; the arrival order of its
elements is a uniform permutation `τ` (arrival `a` is the element `τ a`; this is `ltOf` with values
`τ a`), and the cut is the strict cut `c ∈ {0, …, m}` of the population. `G_j` is (40) with
`P_j` the first `t_j` arrivals. Second sentence: for i.i.d. `U[0,1]` inputs and any deterministic
`q` (the induced cut is `{x > q}`; `q ∉ (0,1)` gives an outer cut), the conditional expectation given
`σ(P_L)` (`HL n`, a sub-σ-algebra) is at most `M_g^L` almost surely; the integrand is integrable. -/
theorem lemma_4_10 : ∀ n, 16 * T ≤ n →
    (∀ c ≤ m n,
      uniformExp (fun τ : Equiv.Perm (Fin (m n)) =>
          Real.exp (1 / 32768 * GSum n (ltOf (fun i : Fin (m n) => (i : ℝ)) τ 1)
            (rankCut (m n) (ltOf (fun i : Fin (m n) => (i : ℝ)) τ 1) c))) ≤ Mg ^ L n) ∧
    ∀ q : ℝ,
      HL n ≤ MeasurableSpace.pi ∧
      Integrable (fun X : Fin n → ℝ =>
          Real.exp (1 / 32768 * GSum n (iidLt X) (fun a => decide (q < vecVal X a)))) (iidUnif n) ∧
      (iidUnif n)[fun X : Fin n → ℝ =>
          Real.exp (1 / 32768 * GSum n (iidLt X) (fun a => decide (q < vecVal X a))) | HL n]
        ≤ᵐ[iidUnif n] fun _ => Mg ^ L n := by sorry

end RandOrderSort
