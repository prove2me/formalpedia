-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_farkas_affine_form1
-- name    : SteinitzExchange.Duality.farkas_affine_form1
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T13:40:03.384908+00:00
-- url     : https://prove2.me/theorems/84e2d072-a88f-42fb-9cc9-cfa15b2bb6ba
-- title:
--   Affine Farkas lemma, Form 1: feasibility of Ax ≤ b or a nonneg dual infeasibility certificate (SteinitzExchange Duality deep input, port of jmoy/farkas_lean)
-- statement:
--   Affine Farkas lemma (Form 1, as in jmoy/farkas_lean via Fourier-Motzkin elimination): for a finite family of affine inequalities sum_j a i j * x j <= b i (i ranging over a finite type), either the system is feasible (some x satisfies all inequalities), or there exists a nonneg infeasibility certificate y : iota -> R with y >= 0, y != 0, sum_i y i * a i j = 0 for every j, and sum_i y i * b i < 0. The two alternatives are mutually exclusive.
-- source:
--   Port of jmoy/farkas_lean (Fourier-Motzkin elimination, Form 1: Ax <= b feasible xor nonneg dual certificate). Deep input F for the real case of SteinitzExchange.Duality.frank_discrete_separation (Thm 6.5, f6a72521); also unblocks weak_duality (Lemma 6.3) R>=D. See ~/workspace/p2m_harness/triage_steinitz_frank_separation.md section 5, item F.

import Mathlib

namespace SteinitzExchange.Duality

/-- **Affine Farkas lemma, Form 1** (port of `jmoy/farkas_lean`, proved there by
Fourier-Motzkin elimination): for a finite family of affine inequalities
`∑ j, a i j * x j ≤ b i` (`i : ι`, `ι` finite), either the system is feasible, or
there is a nonneg infeasibility certificate `y`: `y ≥ 0`, `y ≠ 0`,
`∑ i, y i * a i j = 0` for every `j`, and `∑ i, y i * b i < 0`.
The two alternatives exclude each other: if `∑ j, a i j * x j ≤ b i` for all `i`
and `y ≥ 0` with `∑ i, y i * a i j = 0` for all `j`, then
`0 = ∑ i, y i * (∑ j, a i j * x j) ≤ ∑ i, y i * b i`,
contradicting `∑ i, y i * b i < 0`.

Mission use: the real-case half of `SteinitzExchange.Duality.frank_discrete_separation`
(Thm 6.5, f6a72521) applies this to the constraint family
`{x(X) ≤ f X, -x(X) ≤ -g X}` over `X : Finset V`; it also supplies the `R ≥ D`
direction of `weak_duality` (Lemma 6.3). Stated as a problem node; the proof is left to a future submission. -/
theorem farkas_affine_form1 {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (b : ι → ℝ) :
    (∃ x : Fin n → ℝ, ∀ i : ι, Finset.sum Finset.univ (fun j => a i j * x j) ≤ b i) ∨
    (∃ y : ι → ℝ, (∀ i : ι, 0 ≤ y i) ∧ y ≠ 0 ∧
      (∀ j : Fin n, Finset.sum Finset.univ (fun i => y i * a i j) = 0) ∧
      Finset.sum Finset.univ (fun i => y i * b i) < 0) := by
  sorry

end SteinitzExchange.Duality
