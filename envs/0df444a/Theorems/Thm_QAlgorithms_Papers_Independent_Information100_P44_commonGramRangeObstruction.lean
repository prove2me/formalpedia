-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_commonGramRangeObstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P44.commonGramRangeObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:42:57.600186+00:00
-- url     : https://prove2.me/theorems/4fb3ba69-9ccd-4e16-acc4-f24620f5e1e9
-- title:
--   Theorem 6: general CP range-inclusion obstruction
-- statement:
--   Let a finite common positive Gram matrix have leading corner $A\succeq0$ on $\mathbb C^d$, compatible coupling blocks $B_\alpha$, and arbitrary remaining blocks $C_{\alpha\beta}$. Suppose $\operatorname{rank}A=r<d$. Then for every coupling block,
--   $$\operatorname{Ran}B_\alpha\subseteq\operatorname{Ran}A,\qquad \operatorname{rank}[A\ B_\alpha]\le r.$$
--   The range condition is equivalent to this rank bound, which is equivalent to vanishing of every $(r+1)$-by-$(r+1)$ minor of the augmented matrix. The case $r=0$ is included and forces every $B_\alpha$ to be zero. These are algebraic compatibility constraints, with no unconditional physical non-genericity conclusion.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 22, Theorem 6: general CP range-inclusion obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.22–23, Theorem 6: all coupling ranges, rank characterizations, and all minors.
The zero-rank case is included and forces every coupling to vanish. -/
theorem commonGramRangeObstruction {d m : ℕ} (n : Fin m → ℕ) (A : Mat d)
    (B : (a : Fin m) → Matrix (Fin d) (Fin (n a)) ℂ)
    (C : (a b : Fin m) → Matrix (Fin (n a)) (Fin (n b)) ℂ)
    (r : ℕ) (hA : A.PosSemidef) (hrank : A.rank = r) (hr : r < d)
    (hpos : (commonGram n A B C).PosSemidef) :
    ∀ a,
      Set.range (B a).mulVec ⊆ Set.range A.mulVec ∧
      (augment A (B a)).rank ≤ r ∧ AllMinorsZero (r+1) (augment A (B a)) ∧
      ((Set.range (B a).mulVec ⊆ Set.range A.mulVec) ↔ (augment A (B a)).rank ≤ r) ∧
      ((augment A (B a)).rank ≤ r ↔ AllMinorsZero (r+1) (augment A (B a))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
