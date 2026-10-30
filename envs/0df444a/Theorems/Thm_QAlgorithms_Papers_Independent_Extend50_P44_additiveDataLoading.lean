-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_additiveDataLoading
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.additiveDataLoading
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:24:33.563994+00:00
-- url     : https://prove2.me/theorems/e550ea52-49a9-4896-adc9-01d645b5e836
-- title:
--   Appendix A.1: lookup–rotate–uncompute additive loading cost (90)–(91)
-- statement:
--   Let $D>0$ real table items have positive maximum magnitude, and let $0<\epsilon<1/2$. Pad the table with known zeros to its minimal binary register. Given the reusable normalized phase-gradient resource used in Appendix A.1, a Clifford+T circuit can approximate the ideal multiplexed RX loader, returning the resource and clean work coherently, with
--   $$ \|CJ-JO_{\rm data}\|_{\rm op}\le\epsilon,\qquad T(C)\le K[D+\ln(1/\epsilon)]. $$
--   Here $J$ appends the resource and clean work, and $K>0$ is absolute, preceding $D$, data values and accuracy. The resource uses $b\le K[1+\ln(1/\epsilon)]$ qubits. Its separate reusable-state preparation is not charged on each invocation. The result is the paper's assembled lookup/rotate/uncompute cost, with the small-D cases handled directly rather than by natural subtraction of two.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 25, Appendix A.1: lookup–rotate–uncompute additive loading cost (90)–(91)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

local instance : DecidableEq QAlgorithms.Gate := Classical.decEq _

/-- PDF pp.25-26, (90)-(91): given a reusable phase-gradient resource, lookup,
rotation, and uncomputation have additive T cost O(D+log(1/epsilon)).
The circuit's action includes coherent return of the supplied resource and clean
work. All constants are absolute, before the table size, values and accuracy.
The source's D-2 primitive count is not used for the small-D cases. -/
theorem additiveDataLoading :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℕ, 0 < D → ∀ a : Fin D → ℝ, 0 < tableMax a →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∃ b work : ℕ,
      ∃ c : QAlgorithms.Circuit cliffordTSet (1 + Nat.clog 2 D + b + work),
        1 ≤ b ∧ (b : ℝ) ≤ K * (1 + Real.log (1 / epsilon)) ∧
        QAlgorithms.specNorm
          (QAlgorithms.Circuit.unitary c * loaderEmbedding (Nat.clog 2 D) b work -
            loaderEmbedding (Nat.clog 2 D) b work * idealLoader (paddedTable a)) ≤ epsilon ∧
        (tCount (loaderTWord c) : ℝ) ≤ K * ((D : ℝ) + Real.log (1 / epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
