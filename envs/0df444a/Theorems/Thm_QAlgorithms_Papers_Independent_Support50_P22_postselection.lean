-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P22_postselection
-- name    : QAlgorithms.Papers.Independent.Support50.P22.postselection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:48:12.300874+00:00
-- url     : https://prove2.me/theorems/17356ad9-b2da-4749-b4e9-468c86e928c2
-- title:
--   Theorem 1: postselection bound
-- statement:
--   Let $H$ have positive dimension $d$, let $n\ge0$, and set
--   $$
--   g_{n,d}=\binom{n+d^2-1}{n}.
--   $$
--   Let $\tau_{H^n}=\int\sigma_H^{\otimes n}\,d\mu(\sigma_H)$, where $\mu$ is the Hilbert–Schmidt induced probability law obtained by reducing a Haar pure state on $H\otimes K$, with $K\cong H$. Fix any normalized purification $\psi_{H^nR}$ of this state before choosing the map. Let $\Delta:\operatorname{End}(H^{\otimes n})\to\operatorname{End}(B)$ be complex-linear, with arbitrary finite nonzero output space $B$. Suppose that for every tensor-factor permutation $\pi$ there is a CPTP output map $K_\pi$ such that $\Delta\circ\operatorname{Ad}(P_\pi)=K_\pi\circ\Delta$. Then
--   $$
--   \|\Delta\|_\diamond\le g_{n,d}\,\|(\Delta\otimes\operatorname{id}_R)(|\psi\rangle\langle\psi|)\|_1,
--   \qquad g_{n,d}\le(n+1)^{d^2-1}.
--   $$
--   The trace norm has no factor $1/2$, and the diamond norm ranges over all complex matrices. This reduces the norm bound to a single fixed purified input.
-- source:
--   Post-selection technique for quantum channels with applications to quantum cryptography, arXiv:0809.3019v1, PDF p. 2, Theorem 1: Post-Selection Theorem (seed paper result)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P22

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P18 (ClassicalOutput)

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixBorelSpace

/-- Theorem 1, PDF p.2; tensor convention in footnote 10 on p.4.
Delta remains arbitrary complex-linear, with arbitrary finite output.
The fixed test purification is quantified before Delta. The source's
state-maximization assertion for arbitrary maps is not used as a definition. -/
theorem postselection (n d : ℕ) (hd : 0 < d)
    {R B : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (psi : EuclideanSpace ℂ (Copies (Fin d) n × R)) (hpsi : FinitePurification psi (deFinettiState n d hd))
    (Delta : Matrix (Copies (Fin d) n) (Copies (Fin d) n) ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hcov : ∀ pi : Equiv.Perm (Fin n), ∃ K : Superop B B, IsChannel K ∧
      ∀ X, Delta (permuteInput pi X) = K (Delta X)) :
    diamond Delta ≤ (factor n d : ℝ) * traceNorm (tensorId Delta (pureDensity psi)) ∧
      factor n d ≤ (n+1) ^ (d^2-1) := by sorry

end QAlgorithms.Papers.Independent.Support50.P22

end
