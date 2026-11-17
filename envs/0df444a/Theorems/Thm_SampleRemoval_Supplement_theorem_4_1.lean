-- Prove2me | Theorems.Thm_SampleRemoval_Supplement_theorem_4_1
-- name    : SampleRemoval.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:22:23.537916+00:00
-- url     : https://prove2.me/theorems/e99e01d6-c9a4-4a4c-895c-9dff46efe3c2
-- title:
--   Theorem 4.1 — exact fixed-effects audits by min-plus convolution
-- statement:
--   Let observations be partitioned into nonempty groups, and suppose the re-estimated full-sample one-way fixed-effects slope is positive. Let $f_g(k)$ be each group's optimal cross-scatter after $k$ deletions, let $\Lambda$ be their min-plus convolution, and let $K^*=\min\{K:\Lambda(K)\le0\}$.
--
--   Then
--
--   $$s_{\mathrm{int}}\ge K^*.$$
--
--   If some minimizer at $K^*$ has positive total retained regressor scatter, then
--
--   $$s_{\mathrm{int}}=K^*=\min\{K:\Lambda(K)\le0\}.$$
--
--   In particular, $\Lambda(K^*)<0$ implies this nondegeneracy. The theorem also supplies the truncated min-plus recurrence, its doubling schedule and back-pointers: given the group curves, it computes $K^*$ and an optimal deletion set in $O(nK^*)$ unit-cost comparisons. When every $n_g\le T$, enumerating each group's subsets computes all curves in $O(n2^T)$ steps.
--
--   Differences from the source:
--   - encoding: a finite-valued $s_{\mathrm{int}}$ written as a minimum → $s_{\mathrm{int}}\in\mathbb N\cup\{+\infty\}$, equal to the source minimum whenever a defined nonpositive retained fit exists; reason: preserves the no-feasible-audit case instead of Lean's junk natural-number empty infimum
--   - encoding: $O(nK^*)$ and $O(n2^T)$ arithmetic time → the proof's exact DP recurrence, doubling caps, back-pointer output, subset scan, and a fixed constant 16 in a unit-cost comparison model; reason: makes both asymptotic claims nonvacuous and instance-uniform
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_IsNondegenerate
import Definitions.Def_SampleRemoval_Supplement_fixedSInt
import Definitions.Def_SampleRemoval_Supplement_dpWork

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- **Theorem 4.1 (Exact audits for fixed-effects regressions).** Positive full-sample slope gives
the min-plus lower bound; a nondegenerate minimizer at `K*` gives equality. The min-plus dynamic
program with doubling and back-pointers uses `O(n K*)` unit-cost comparisons, and group curves
for groups of size at most `T` use `O(n 2^T)` subset-enumeration steps (Xu, Gao, Hu,
*Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission,
manuscript sha256 `dcd33ace…`, Theorem 4.1, p.7 (PDF p.9)).

**Formalization Note** Every group is nonempty, as it is a block of the stated partition. The
full-sample slope hypothesis explicitly includes positive total `V`, so the quotient is defined.
`fixedSInt` is `WithTop ℕ`, preserving the value `+∞` if no deletion leaves a defined
nonpositive slope. The DP table below is the recurrence from the proof, in `WithTop ℝ` so
infeasible states have value `⊤`; `cap` is the exact doubling schedule; `dpWork` counts every
candidate comparison. The fixed constant `16` witnesses the two Big-O bounds independently of
the instance. The final existential subsets are the back-pointer output. -/
theorem theorem_4_1 {Γ : ℕ} (M : FixedEffectsModel Γ)
    (hgroups : ∀ g, 0 < M.nobs g)
    (hfull :
      0 < ∑ g, withinXScatter M g Finset.univ ∧
      0 < (∑ g, withinCross M g Finset.univ) / (∑ g, withinXScatter M g Finset.univ)) :
    ((fixedKStar M : WithTop ℕ) ≤ fixedSInt M) ∧
    (IsNondegenerate M →
      fixedSInt M = (fixedKStar M : WithTop ℕ) ∧
      ∃ A : (g : Fin Γ) → Finset (Fin (M.nobs g)),
        ∑ g, (M.nobs g - (A g).card) = fixedKStar M ∧
        0 < ∑ g, withinXScatter M g (A g) ∧
        ∑ g, withinCross M g (A g) ≤ 0) ∧
    (minPlus M (fixedKStar M) < 0 → IsNondegenerate M) ∧
    (∃ (r : ℕ) (cap : Fin (r + 1) → ℕ)
        (D : Fin (Γ + 1) → ℕ → WithTop ℝ),
      let lastCap := cap ⟨r, Nat.lt_succ_self r⟩
      cap ⟨0, Nat.zero_lt_succ r⟩ = 1 ∧
      (∀ j : Fin r, cap j.succ = min (totalObs M) (2 * cap j.castSucc)) ∧
      (∀ j : Fin r, cap j.castSucc < fixedKStar M) ∧
      fixedKStar M ≤ lastCap ∧ lastCap < 2 * fixedKStar M ∧
      (∑ j, dpWork M (cap j)) ≤ 16 * totalObs M * fixedKStar M ∧
      (∀ K, D ⟨0, Nat.zero_lt_succ Γ⟩ K = if K = 0 then 0 else ⊤) ∧
      (∀ (j : Fin Γ) (K : ℕ), K ≤ lastCap →
        D j.succ K = sInf {z : WithTop ℝ | ∃ k : ℕ, k ≤ min (M.nobs j) K ∧
          z = D j.castSucc (K - k) + (deletionCurve M j k : WithTop ℝ)}) ∧
      (∀ K, K ≤ lastCap →
        D ⟨Γ, Nat.lt_succ_self Γ⟩ K = (minPlus M K : WithTop ℝ))) ∧
    (∀ T : ℕ, (∀ g, M.nobs g ≤ T) →
      (∑ g, 2 ^ M.nobs g) ≤ totalObs M * 2 ^ T ∧
      ∀ (g : Fin Γ) (k : ℕ), k ≤ M.nobs g →
        ∃ A : Finset (Fin (M.nobs g)),
          A.card = M.nobs g - k ∧ withinCross M g A = deletionCurve M g k) := by sorry

end SampleRemoval.Supplement
