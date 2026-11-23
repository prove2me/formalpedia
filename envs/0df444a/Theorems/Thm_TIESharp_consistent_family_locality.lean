-- Prove2me | Theorems.Thm_TIESharp_consistent_family_locality
-- name    : TIESharp.consistent_family_locality
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:47:11.818607+00:00
-- url     : https://prove2.me/theorems/990a8c85-7268-4085-80fa-eadaaccb4c38
-- title:
--   Locality of the common limit for a consistent family
-- statement:
--   Let $n\ge2$ and let $F$ be a feasible, truthful-in-expectation, $R$-approximate family that is consistent under insertion of zero-cost jobs. Then there are measurable functions
--   $$g_i:(0,\infty)^n\to[0,1]$$
--   and measurable limiting assignment laws $y^{m,*}$ with the following properties almost everywhere on the strictly positive orthant:
--
--   * the weights are nonnegative and sum to one;
--   * $q^{m,*}_{ij}(t)=g_i(t_{\cdot j})$;
--   * $\sum_Ay^{m,*}_A(t)C_{\max}(t,A)\le R\,\mathrm{OPT}(t)$;
--   * the laws are equivariant under permutations of machines and jobs.
--
--   This isolates the second and longer stage of Theorem 3.1 after free-job consistency has been obtained. Lemma 4.3 constructs the limit, Lemma 4.4 kills higher-order interactions, Lemma 4.5 obtains the corresponding kernel expansion, and pairwise independence of the kernels gives column locality. The approximation bound and the symmetries survive the limit.
--
--   **Formalization Note.** This is not an additional hypothesis: it follows from the precisely cited arguments of §§4.2–4.4. The statement deliberately retains only the weak measurability/regularity guaranteed by those arguments and not any Lipschitz formulas that Lemma 4.3 disclaims.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Theorem 3.1 and §§4.2–4.4, especially the “Completion of the proof of Theorem 3.1”, pp.5 and 16–23

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox
import Definitions.Def_TIESharp_IsConsistentFamily

set_option autoImplicit false

open MeasureTheory

/-- **Locality theorem for a consistent family** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §§4.2–4.4, pp.16–23).
If `F` is feasible, truthful in expectation, `R`-approximate, and consistent under adding
zero-cost jobs, then its common subdiagonal limit is column-local: there are measurable
one-column functions `g_i` in `[0,1]` and measurable limiting assignment laws whose marginal at
`(i,j)` is `g_i` of column `j`. The laws are probability distributions, retain the ratio `R`, and
are equivariant under machine and job permutations, almost everywhere on the positive orthant. -/
theorem TIESharp.consistent_family_locality (n : ℕ) (hn : 2 ≤ n) (R : ℝ)
    (F : TIESharp.Family n) (hF : TIESharp.IsFeasible F) (hT : TIESharp.IsTIE F)
    (hR : TIESharp.IsRApprox F R) (hcon : TIESharp.IsConsistentFamily F) :
    ∃ g : Fin n → (Fin n → ℝ) → ℝ,
      (∀ i, Measurable (g i)) ∧
      (∀ i (c : Fin n → ℝ), (∀ a, 0 < c a) → g i c ∈ Set.Icc 0 1) ∧
      ∃ yStar : (m : ℕ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n) → ℝ,
        (∀ (m : ℕ) (A : Fin m → Fin n), Measurable (fun t => yStar m t A)) ∧
        ∀ m : ℕ, 1 ≤ m →
          (∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
            (∀ A, 0 ≤ yStar m t A) ∧ ∑ A, yStar m t A = 1 ∧
            (∀ i j, ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), yStar m t A
              = g i (fun a => t a j)) ∧
            ∑ A, yStar m t A * MatousekLP.Scheduling.makespan (Matrix.of t) A
              ≤ R * TIESharp.opt t) ∧
          ∀ (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin m)),
            ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
              ∀ A : Fin m → Fin n,
                yStar m (fun i j => t (σ.symm i) (π.symm j)) (σ ∘ A ∘ π.symm)
                  = yStar m t A := by sorry
