-- Prove2me | Theorems.Thm_TranspositionIID_Main_lemma_2_2
-- name    : TranspositionIID.Main.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:15.990213+00:00
-- url     : https://prove2.me/theorems/1d9bdaed-af55-4605-a053-c11bd6b57ab5
-- title:
--   Lemma 2.2 — excess cost from separated inversions
-- statement:
--   Let $n\ge1$ and let $p$ be a decreasing strictly positive probability vector. For every list $\sigma$,
--   $$F_p(\sigma)\le2+(1+\sqrt e)\int_{-\infty}^{0}e^xJ_x(\sigma)\,dx.$$
--   The integral is finite. This bounds excess search cost using precisely the separated inversion counts of §2.3.
--
--   Differences from the source:
--   - encoding: labels and charged positions 1 through n → labels and positions Fin n with charged position val + 1; reason: the order-preserving shift gives a bijection of all labels and list states
--   - encoding: decreasing relabeling with OPT equal to the sorted positional cost → OPT is the attained minimum over all permutations; reason: sorting shows these are identical, including ties and zeros; no label order is required by the goal
--   - encoding: the finite improper integral over minus infinity to zero → the Lebesgue integral on Iic 0 with integrability asserted in the conclusion; reason: the endpoint has measure zero and explicit integrability prevents a default zero for a divergent integral
--   - encoding: r is the unique positive root of equation (2.2) → r is the infimum of its nonnegative upper level set; reason: continuity and strict increase above zero identify this finite infimum with that root for n at least one
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Lemma 2.2, printed p.4 = PDF p.4; source.pdf SHA256 07dbf227a79b9907070bc1c27f25a0848cee3135ec65bcf105159f991b3b4545.

import Definitions.Def_TranspositionIID_Main_Buffer

namespace TranspositionIID.Main

/-- Lemma 2.2, printed/PDF p.4. The integral is finite, not a default Bochner value. -/
theorem lemma_2_2 {n : ℕ} (hn : 1 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i) (σ : ListState n) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp x * adaptiveInversions p x σ) (Set.Iic 0) ∧
    excess p σ ≤ 2 + (1 + Real.sqrt (Real.exp 1)) *
      (∫ x : ℝ in Set.Iic 0, Real.exp x * adaptiveInversions p x σ) := by sorry

end TranspositionIID.Main
