-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_matthewsWehnerComparison
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.matthewsWehnerComparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:35:11.918237+00:00
-- url     : https://prove2.me/theorems/fe9b8245-a82c-4d77-a864-9dca412225fb
-- title:
--   Proposition 6: comparison with Matthews–Wehner, including strictness
-- statement:
--   Let $\mathcal N:A\to B$ be a finite CPTP channel on nonzero registers, and $0\le e<1$. Let $\phi_\rho$ be the canonical purification of a density input $\rho$, and let $D_H^e$ be binary hypothesis-testing relative entropy in bits, allowing $+\infty$ at zero type-II error. Its PPT version restricts both measurement effects to be PPT. Then
--
--   $$C_{\mathrm{NS}}^{(1)}\le R_E=\max_\rho\min_\sigma D_H^e((\mathrm{id}\otimes\mathcal N)\phi_\rho\Vert\rho_{A'}\otimes\sigma),$$
--
--   $$C_{\mathrm{NS}\cap\mathrm{PPT}}^{(1)}\le R_{E\cap\mathrm{PPT}}=\max_\rho\min_\sigma D_{H,\mathrm{PPT}}^e((\mathrm{id}\otimes\mathcal N)\phi_\rho\Vert\rho_{A'}\otimes\sigma).$$
--
--   All capacities and bounds refer to $(\mathcal N,e)$. Each illustrated family—amplitude damping and the binary cq channel with pure outputs $a|0\rangle\pm\sqrt{1-a^2}|1\rangle$—contains parameters and an error threshold where both inequalities are strict. No exact numerical witnesses are prescribed. These comparisons sharpen the earlier finite-blocklength converse.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 10, Proposition 6

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF pp.10–12, Proposition 6: both comparisons, their max-min testing
expressions, and existence of strict examples in EACH illustrated family.
The strict witnesses are existential, not invented rational points from plots. -/
theorem matthewsWehnerComparison [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    (∀ ppt : Bool, oneShot ppt N e ≤ mwBound ppt N e ∧
      (mwBound ppt N e : EReal) = mwTesting ppt N e ∧ MWTestingAttained ppt N e) ∧
    (∃ gamma eps : ℝ, 0 ≤ gamma ∧ gamma ≤ 1 ∧ 0 < eps ∧ eps < 1 ∧
      oneShot false (AD gamma) eps < mwBound false (AD gamma) eps ∧
      oneShot true (AD gamma) eps < mwBound true (AD gamma) eps) ∧
    (∃ a eps : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ Real.sqrt (1 - a^2) ≤ a ∧
      0 < eps ∧ eps < 1 ∧
      oneShot false (simpleCQ a) eps < mwBound false (simpleCQ a) eps ∧
      oneShot true (simpleCQ a) eps < mwBound true (simpleCQ a) eps) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
