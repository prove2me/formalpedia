-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_normalized_sector_fidelity
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.normalized_sector_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:06:37.498975+00:00
-- url     : https://prove2.me/theorems/3752cc82-c890-4434-86b3-f694a9abda88
-- title:
--   Normalized emission-sector relative-frequency fidelity
-- statement:
--   Let $A,m,l$ be nonnegative integers with $l\le A$ and $m+l>0$. In the normalized vector $F_l$ of (19), define $F$ as the Born expectation of the fraction of photons in mode $a_1$. Then
--
--   $$
--   F=\binom{m+l+1}{l}^{-1}\sum_{i=0}^l\binom{m+l-i}{m}\frac{m+l-i}{m+l}
--   =\frac{m(m+2)+l(m+1)}{(m+l)(m+2)}
--   =\frac{Mm+M+m}{M(m+2)},\quad M=m+l.
--   $$
--
--   This evaluates the relative frequency of the actual normalized sector, not an arbitrary real variable. It gives $5/6$ when $m=l=1$, unity at $l=0,m>0$, and $1/2$ for the vacuum-seeded algebraic case $m=0,l>0$. The empty-photon frequency is excluded. The formula identifies the fidelity attained by the fixed-count physical branches.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 5, Sec. II C, Eq.(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5 Eq.(20): relative frequency of a1 in the normalized sector.
The no-photon case m=l=0 is excluded; vacuum seeding with l>0 has value 1/2. -/
theorem normalized_sector_fidelity (A m l : ℕ) (hlA : l ≤ A) (hM : 0 < m + l) :
    IsState (emissionSectorKet A m l) ∧
    sectorFidelity A m l =
      (Nat.choose (m + l + 1) l : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (l + 1),
          (Nat.choose (m + l - i) m : ℝ) * ((m + l - i : ℕ) : ℝ) / (m + l) ∧
    sectorFidelity A m l =
      (((m * (m + 2) + l * (m + 1) : ℕ) : ℝ) / ((m + l : ℕ) * (m + 2) : ℝ)) ∧
    sectorFidelity A m l = benchmark m (m + l) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
