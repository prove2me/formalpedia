-- Prove2me | Theorems.Thm_TIESharp_theorem_3_1
-- name    : TIESharp.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:38:37.304606+00:00
-- url     : https://prove2.me/theorems/791982c2-5eaf-4ce1-b4da-a97bc4eb3f59
-- title:
--   Theorem 3.1 — locality of a limiting family: $q^{m,*}_{ij}(t)=g_i(t_{\cdot j})$ with ratio $R$
-- statement:
--   Fix $n\ge2$ and a truthful-in-expectation family with finite uniform approximation ratio $R$. There exist measurable functions $g_i:(0,\infty)^n\to[0,1]$ and, for each $m\ge1$, a measurable assignment distribution $y^{m,*}$ with marginals $q^{m,*}_{ij}$, defined for almost every $t\in(0,\infty)^{n\times m}$, such that for all $i\in[n]$ and $j\in[m]$,
--   $$q^{m,*}_{ij}(t)=g_i(t_{\cdot j}),\qquad \sum_A y^{m,*}_A(t)\,C_{\max}(t,A)\le R\,\mathrm{OPT}(t).$$
--   The same one-column functions $g_i$ apply to every job $j$ at every job count $m$. The assignment laws and their marginals are equivariant under job and machine permutations up to null sets.
--
--   This column-locality is what lets the lower-bound argument treat each spoke of the star instance in isolation.
--
--   Differences from the source:
--   - encoding: a measurable assignment distribution defined for almost every t → weights yStar m t A measurable in t for each A, a probability vector a.e. on the open orthant; reason: Lean convention for an a.e.-defined distribution on a finite set
--   - encoding: the laws and their marginals are equivariant up to null sets → the laws are equivariant a.e. for every machine and job permutation; reason: equivariance of the marginals follows by summing the laws
--   - encoding: a family: one assignment distribution and one finite expected-payment vector per job count, on bids in [0,∞)^{n×m} → Family n with real weights alloc and real payments pay, plus IsFeasible (weights nonnegative and summing to one at every nonnegative bid profile); values at profiles with a negative entry are unconstrained; reason: Lean convention for a distribution on the finite set of assignments; same families
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Theorem 3.1, p.5

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox

set_option autoImplicit false

open MeasureTheory

namespace TIESharp

/-- **Theorem 3.1 (Locality of a limiting family)** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Theorem 3.1, p.5). Fix `n ≥ 2` and a
truthful-in-expectation family with finite uniform approximation ratio `R`. There exist measurable
functions `g_i : (0, ∞)^n → [0, 1]` and, for each `m ≥ 1`, a measurable assignment distribution
`y^{m,*}` with marginals `q^{m,*}_ij`, defined for almost every `t ∈ (0, ∞)^{n×m}`, such that for
all `i ∈ [n]` and `j ∈ [m]`,
`q^{m,*}_ij(t) = g_i(t_{·j})` and `Σ_A y^{m,*}_A(t) C_max(t, A) ≤ R · OPT(t)`.
The same one-column functions `g_i` apply to every job `j` at every job count `m`. The assignment
laws and their marginals are equivariant under job and machine permutations up to null sets.

**Formalization Note.** `y^{m,*}` is a weight function on assignments, measurable in the profile
for each assignment; "a distribution ... defined for almost every t" is: a.e. on the open orthant
it is a probability vector. Equivariance of the laws implies that of their marginals. -/
theorem theorem_3_1 (n : ℕ) (hn : 2 ≤ n) (F : Family n) (R : ℝ) (hF : IsFeasible F)
    (hT : IsTIE F) (hR : IsRApprox F R) :
    ∃ g : Fin n → (Fin n → ℝ) → ℝ,
      (∀ i, Measurable (g i)) ∧ (∀ i (c : Fin n → ℝ), (∀ a, 0 < c a) → g i c ∈ Set.Icc 0 1) ∧
    ∃ yStar : (m : ℕ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n) → ℝ,
      (∀ (m : ℕ) (A : Fin m → Fin n), Measurable (fun t => yStar m t A)) ∧
      ∀ m : ℕ, 1 ≤ m →
        (∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
          (∀ A, 0 ≤ yStar m t A) ∧ ∑ A, yStar m t A = 1 ∧
          (∀ i j, ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), yStar m t A
            = g i (fun a => t a j)) ∧
          ∑ A, yStar m t A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ R * opt t) ∧
        ∀ (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin m)),
          ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
            ∀ A : Fin m → Fin n,
              yStar m (fun i j => t (σ.symm i) (π.symm j)) (σ ∘ A ∘ π.symm) = yStar m t A := by sorry

end TIESharp
