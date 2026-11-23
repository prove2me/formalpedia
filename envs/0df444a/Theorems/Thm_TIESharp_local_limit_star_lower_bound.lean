-- Prove2me | Theorems.Thm_TIESharp_local_limit_star_lower_bound
-- name    : TIESharp.local_limit_star_lower_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:32:10.026852+00:00
-- url     : https://prove2.me/theorems/39adfe38-8c6a-497f-b873-0c6b0b6c2945
-- title:
--   Perturbed-star lower bound for a column-local limiting family
-- statement:
--   Fix $n\ge2$ machines. Suppose that measurable functions $g_i:(0,\infty)^n\to[0,1]$ describe the probability that machine $i$ receives a job as a function of that job's column alone. At every job count $m\ge1$, let $y^{m,*}$ be measurable limiting assignment weights defined almost everywhere on the positive orthant. Assume that, almost everywhere, these weights are nonnegative and sum to one, their marginals are $q^{m,*}_{ij}(t)=g_i(t_{\cdot j})$, and
--   $$
--   \sum_A y^{m,*}_A(t)C_{\max}(t,A)\le R\,\mathrm{OPT}(t).
--   $$
--   Assume moreover that the laws are equivariant under permutations of machines and jobs, up to null sets. Then
--   $$
--   R\ge \frac{n+1}{2}.
--   $$
--
--   This is precisely the probabilistic star argument in the proof of Theorem 3.2. Independently perturb every entry of the star profile with low uniform costs near $1$ at its endpoints and high uniform costs near $t$ elsewhere. The one-job guarantee forces almost all endpoint probability; machine symmetry splits a spoke's endpoint probability equally. Column locality then makes the root's expected load on the full star approach $1+(n-1)/2$ as $t\to\infty$, while the approximation guarantee bounds it by $R(1+\tau)$. Taking $t\to\infty$ and $\tau\downarrow0$ proves the inequality.
--
--   **Formalization Note.** The statement isolates exactly the output of Theorem 3.1, so the lower-bound calculation can be proved independently of the limiting-family construction. Almost-everywhere assertions use Lebesgue measure restricted to the strictly positive orthant.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), proof of Theorem 3.2, “The profile distribution”, “A job in isolation”, and “The full star”, pp.6–8

import Mathlib
import Definitions.Def_TIESharp_opt

set_option autoImplicit false

open MeasureTheory

/-- **Perturbed-star lower bound for a column-local limiting family** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, proof of Theorem 3.2, pp.6–8).
Given measurable one-column probabilities `g_i` valued in `[0,1]` on the positive orthant and,
at every positive job count, measurable limiting assignment laws with those marginals, probability
normalization and approximation ratio `R` almost everywhere, as well as machine equivariance,
the ratio satisfies `R ≥ (n+1)/2`. -/
theorem TIESharp.local_limit_star_lower_bound (n : ℕ) (hn : 2 ≤ n) (R : ℝ)
    (g : Fin n → (Fin n → ℝ) → ℝ)
    (hgmeas : ∀ i, Measurable (g i))
    (hg01 : ∀ i (c : Fin n → ℝ), (∀ a, 0 < c a) → g i c ∈ Set.Icc 0 1)
    (yStar : (m : ℕ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n) → ℝ)
    (hymeas : ∀ (m : ℕ) (A : Fin m → Fin n), Measurable (fun t => yStar m t A))
    (hy : ∀ m : ℕ, 1 ≤ m →
      (∀ᵐ t ∂(MeasureTheory.volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
        (∀ A, 0 ≤ yStar m t A) ∧ ∑ A, yStar m t A = 1 ∧
        (∀ i j, ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), yStar m t A
          = g i (fun a => t a j)) ∧
        ∑ A, yStar m t A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ R * opt t) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin m)),
        ∀ᵐ t ∂(MeasureTheory.volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
          ∀ A : Fin m → Fin n,
            yStar m (fun i j => t (σ.symm i) (π.symm j)) (σ ∘ A ∘ π.symm) = yStar m t A) :
    ((n : ℝ) + 1) / 2 ≤ R := by sorry
