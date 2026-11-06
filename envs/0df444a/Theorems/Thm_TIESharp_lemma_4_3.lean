-- Prove2me | Theorems.Thm_TIESharp_lemma_4_3
-- name    : TIESharp.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:39:34.511212+00:00
-- url     : https://prove2.me/theorems/5d2c9791-e19f-430e-94ce-ac8c12ec9765
-- title:
--   Lemma 4.3 — a common measurable weak-star limit across all job counts
-- statement:
--   Let $n\ge2$ and let $F$ be a feasible, truthful-in-expectation, $R$-approximate family with the consistency properties of Lemma 4.2. Let $G_h$ floor every report coordinate to the nonnegative $h$-grid. There is one sequence $h_\ell=1/k_\ell\downarrow0$ ($k_\ell$ strictly increasing positive integers) and measurable functions $y^{m,*}_A$, $V^{m,*}_i$ such that:
--   1. at every job count, the grid approximations $y^m\circ G_{h_\ell}$, $q^m\circ G_{h_\ell}$ and $V^m_i\circ G_{h_\ell}$ converge weak-star on every bounded profile box to $y^{m,*}$, to its marginals $q^{m,*}_{ij}=\sum_{A:A(j)=i}y^{m,*}_A$, and to $V^{m,*}_i$;
--   2. almost everywhere on $(0,\infty)^{n\times m}$, $y^{m,*}(t)$ is a probability vector satisfying the performance bound
--   $$\sum_A y^{m,*}_A(t)\,C_{\max}(t,A)\le R\,\mathrm{OPT}(t),$$
--   and the limits are equivariant under job and machine permutations;
--   3. $\partial_{ij}V^{m,*}_i=q^{m,*}_{ij}$ in the distributional sense on the open orthant;
--   4. components lifted from subprofiles by ignoring omitted columns converge weak-star to the lifted limits, and every finite constant-coefficient linear identity $\sum_r a_r f_r=a_0$ between (lifted) grid approximations that holds almost everywhere on a box for all large $\ell$ holds almost everywhere on that box for the limits.
--
--   The original family need not be measurable; the limit is, and it keeps the original ratio $R$.
--
--   Differences from the source:
--   - generalization: one sequence h_ℓ ↓ 0 → h_ℓ = 1/k_ℓ with k strictly increasing positive integers; reason: the proof builds exactly such a sequence (p.17, "For h = 1/k"); it implies the printed existence
--   - generalization: finite linear identities between the grid approximations survive the extraction → an identity Σ a_r f_r = a₀ holding a.e. on a box for all large ℓ holds a.e. on the box for the limits; reason: a weaker hypothesis (a.e., eventually) and an affine constant; the printed identities are special cases
--   - encoding: weak-star convergence on every bounded profile box → WeakStarTendsto on the boxes (0, M)^{n×m}, M > 0, against all L¹ tests, with measurability and uniform boundedness on each box; reason: as defined on p.17; every bounded box in the orthant lies in such a box
--   - encoding: ∂_ij V^{m,*}_i = q^{m,*}_ij in the distributional sense → IsWeakPartial on the open orthant with C^∞ compactly supported tests; reason: the test class of the proof (4.5)–(4.6)
--   - encoding: a family: one assignment distribution and one finite expected-payment vector per job count, on bids in [0,∞)^{n×m} → Family n with real weights alloc and real payments pay, plus IsFeasible (weights nonnegative and summing to one at every nonnegative bid profile); values at profiles with a negative entry are unconstrained; reason: Lean convention for a distribution on the finite set of assignments; same families
--   - generalization: the normalized family of Lemma 4.2 → any feasible, truthful-in-expectation, R-approximate family with the Lemma 4.2 properties (IsConsistentFamily), normalized or not; reason: potentials and normalized payments are computed from p̄, which the normalization does not change, so the family of Lemma 4.2 is an instance
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.3, p.16 (grid h = 1/k from §4.2.1, p.17)

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox
import Definitions.Def_TIESharp_IsConsistentFamily
import Definitions.Def_TIESharp_potential
import Definitions.Def_TIESharp_floorGrid
import Definitions.Def_TIESharp_WeakStarTendsto
import Definitions.Def_TIESharp_IsWeakPartial
import Definitions.Def_TIESharp_liftComp

set_option autoImplicit false

open MeasureTheory Filter

namespace TIESharp

/-- **Lemma 4.3 (A common measurable limit)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Lemma 4.3, p.16). Let `n ≥ 2` and let `F` be a feasible,
truthful-in-expectation, `R`-approximate family with the consistency properties of Lemma 4.2. Let
`G_h` floor every report coordinate to the nonnegative `h`-grid, `h = 1/k`. There is one sequence
`h_ℓ = 1/k_ℓ ↓ 0` (`k_ℓ` strictly increasing positive integers) and measurable limits `y^{m,*}`,
`V^{m,*}_i` such that:
1. at every job count, the grid approximations `y^m ∘ G_h`, `q^m ∘ G_h`, `V^m_i ∘ G_h` converge
   weak-star on every bounded profile box to `y^{m,*}`, its marginals `q^{m,*}`, and `V^{m,*}_i`;
2. almost everywhere on the open orthant `(0, ∞)^{n×m}`, `y^{m,*}(t)` is a probability vector with
   `Σ_A y^{m,*}_A(t) C_max(t, A) ≤ R · OPT(t)`, and the limits are equivariant under machine and
   job permutations;
3. `∂_ij V^{m,*}_i = q^{m,*}_ij` in the distributional sense on the open orthant;
4. components lifted from subprofiles by ignoring omitted columns also converge weak-star, and every
   finite constant-coefficient linear identity between (lifted) grid approximations on a box
   survives the extraction.

**Formalization Note.** Weak-star convergence is `WeakStarTendsto` (boxes `(0, M)^{n×m}`, all
`L¹` tests). In item 4 a component is `(m', e, κ)` with `e : Fin m' ↪o Fin m` (`liftComp`); the
identity `Σ_r a_r f_r = a₀` is assumed a.e. on the box for all large `ℓ` and concluded a.e. for the
limits. -/
theorem lemma_4_3 (n : ℕ) (hn : 2 ≤ n) (F : Family n) (R : ℝ) (hF : IsFeasible F)
    (hT : IsTIE F) (hR : IsRApprox F R) (hC : IsConsistentFamily F) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ 0 < k 0 ∧
    ∃ (yStar : (m : ℕ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n) → ℝ)
      (VStar : (m : ℕ) → (Fin n → Fin m → ℝ) → Fin n → ℝ),
      (∀ (m : ℕ) (A : Fin m → Fin n), Measurable (fun t => yStar m t A)) ∧
      (∀ (m : ℕ) (i : Fin n), Measurable (fun t => VStar m t i)) ∧
      (∀ (m : ℕ) (A : Fin m → Fin n),
        WeakStarTendsto (fun ℓ t => F.alloc m (floorGrid (1 / (k ℓ : ℝ)) t) A)
          (fun t => yStar m t A)) ∧
      (∀ (m : ℕ) (i : Fin n) (j : Fin m),
        WeakStarTendsto (fun ℓ t => marg F m (floorGrid (1 / (k ℓ : ℝ)) t) i j)
          (fun t => ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), yStar m t A)) ∧
      (∀ (m : ℕ) (i : Fin n),
        WeakStarTendsto (fun ℓ t => potential F m (floorGrid (1 / (k ℓ : ℝ)) t) i)
          (fun t => VStar m t i)) ∧
      (∀ m : ℕ, ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
        (∀ A, 0 ≤ yStar m t A) ∧ ∑ A, yStar m t A = 1 ∧
        ∑ A, yStar m t A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ R * opt t) ∧
      (∀ (m : ℕ) (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin m)),
        ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
          (∀ A : Fin m → Fin n,
            yStar m (fun i j => t (σ.symm i) (π.symm j)) (σ ∘ A ∘ π.symm) = yStar m t A) ∧
          ∀ i, VStar m (fun i' j => t (σ.symm i') (π.symm j)) (σ i) = VStar m t i) ∧
      (∀ (m : ℕ) (i : Fin n) (j : Fin m),
        IsWeakPartial (fun t => VStar m t i)
          (fun t => ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), yStar m t A)
          i j) ∧
      (∀ (m : ℕ) (c : Σ m' : ℕ, (Fin m' ↪o Fin m) × ((Fin m' → Fin n) ⊕ Fin n)),
        WeakStarTendsto
          (fun ℓ t => liftComp (fun m' b A => F.alloc m' (floorGrid (1 / (k ℓ : ℝ)) b) A)
            (fun m' b i => potential F m' (floorGrid (1 / (k ℓ : ℝ)) b) i) c t)
          (liftComp yStar VStar c)) ∧
      (∀ (m r : ℕ) (c : Fin r → Σ m' : ℕ, (Fin m' ↪o Fin m) × ((Fin m' → Fin n) ⊕ Fin n))
          (a : Fin r → ℝ) (a₀ M : ℝ), 0 < M →
        (∀ᶠ ℓ in atTop,
          ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M}),
            ∑ s, a s * liftComp (fun m' b A => F.alloc m' (floorGrid (1 / (k ℓ : ℝ)) b) A)
              (fun m' b i => potential F m' (floorGrid (1 / (k ℓ : ℝ)) b) i) (c s) t = a₀) →
        ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, t i j ∈ Set.Ioo 0 M}),
          ∑ s, a s * liftComp yStar VStar (c s) t = a₀) := by sorry

end TIESharp
