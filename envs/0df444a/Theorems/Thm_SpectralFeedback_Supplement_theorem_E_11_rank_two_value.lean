-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_E_11_rank_two_value
-- name    : SpectralFeedback.Supplement.theorem_E_11_rank_two_value
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:00:25.624727+00:00
-- url     : https://prove2.me/theorems/3ea4b1a3-c4ef-4e66-96aa-d3f0bd52de09
-- title:
--   Theorem E.11 — two-symbol, rank-two value $G_{2,2}(\rho)=\sqrt{(\lambda_1+\lambda_4)(\lambda_2+\lambda_3)}$
-- statement:
--   Let $\rho\succeq0$ be a complex $d\times d$ matrix with $d\ge2$, and let $\lambda_1\ge\lambda_2\ge\lambda_3\ge\lambda_4$ be its four largest eigenvalues, padded by zeros when $d<4$. Then, without normalization of their sum,
--
--   $$
--   G_{2,2}(\rho)=\sqrt{(\lambda_1+\lambda_4)(\lambda_2+\lambda_3)}.\qquad\text{(E.23)}
--   $$
--
--   In a decreasing spectral basis $(e_i)$ set
--
--   $$
--   v_{1,\pm}=\frac{\sqrt{\lambda_1}e_1\pm\sqrt{\lambda_4}e_4}{\sqrt2},\qquad v_{2,\pm}=\frac{\sqrt{\lambda_2}e_2\pm\sqrt{\lambda_3}e_3}{\sqrt2},\qquad T_\pm=\sum_{i=1}^2v_{i,\pm}v_{i,\pm}^*,
--   $$
--
--   ignoring zero-padded coordinates. Then $A_+=T_++\sum_{i>4}\lambda_ie_ie_i^*$ and $A_-=T_-$ are optimal: both are positive semidefinite, $A_++A_-=\rho$, and $f_2(A_+)+f_2(A_-)=\sqrt{(\lambda_1+\lambda_4)(\lambda_2+\lambda_3)}$.
--
--   Differences from the source:
--   - encoding: the value G_{2,2}(ρ) → IsGreatest (rewardSet 2 (chi 2) 2 ρ); reason: the base mission's convention
--   - encoding: T_± and the tail Σ_{i>4} λ_i e_i e_i* in a spectral basis → the published pairAtom ρ U 2 (±1) and tailPart ρ U 2, for every decreasing spectral basis U; reason: the published definitions are these matrices; coordinates beyond d do not occur in Fin d
--   - encoding: two optimal coarse atoms → A_± positive semidefinite, A_+ + A_− = ρ, total reward equal to the value; reason: that is what optimality of a decomposition means
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem E.11, (E.23), p.87 (PDF p.89)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_pairAtom
import Definitions.Def_SpectralFeedback_Supplement_chi

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem E.11** (Two-symbol, rank-two value; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.87 (PDF p.89)). For every
positive matrix `ρ` of dimension `d ≥ 2`, let `λ_1 ≥ λ_2 ≥ λ_3 ≥ λ_4` be its four largest
eigenvalues, padding by zeros when `d < 4`. Then, without normalization of their sum,
`G_{2,2}(ρ) = √((λ_1 + λ_4)(λ_2 + λ_3))` (E.23). In a spectral basis, set
`v_{1,±} = (√λ_1 e_1 ± √λ_4 e_4)/√2`, `v_{2,±} = (√λ_2 e_2 ± √λ_3 e_3)/√2`,
`T_± = ∑_{i=1}^2 v_{i,±} v_{i,±}*`. Zero padded coordinates are ignored. Two optimal coarse atoms are
`A_+ = T_+ + ∑_{i>4} λ_i e_i e_i*` and `A_− = T_−`.

**Formalization Note** `G_{2,2}(ρ) = v` is `IsGreatest (rewardSet 2 (chi 2) 2 ρ) v`. Eigenvalues are
`eigDesc` (0-based: `λ_1 = eigDesc ρ 0`, …). `T_±` are the published `pairAtom ρ U 2 (±1)` and
`∑_{i>4} λ_i e_i e_i*` is the published `tailPart ρ U 2`, for every decreasing spectral basis `U`;
"optimal coarse atoms" is: both are positive semidefinite, they sum to `ρ`, and their total reward
is the value. -/
theorem theorem_E_11_rank_two_value {d : ℕ} (hd : 2 ≤ d) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) :
    IsGreatest (rewardSet 2 (chi 2) 2 ρ)
        (Real.sqrt ((eigDesc ρ 0 + eigDesc ρ 3) * (eigDesc ρ 1 + eigDesc ρ 2))) ∧
      ∀ U : Matrix (Fin d) (Fin d) ℂ, IsSortedEigenbasis ρ U →
        (pairAtom ρ U 2 1 + tailPart ρ U 2).PosSemidef ∧ (pairAtom ρ U 2 (-1)).PosSemidef ∧
        (pairAtom ρ U 2 1 + tailPart ρ U 2) + pairAtom ρ U 2 (-1) = ρ ∧
        reward 2 (chi 2) (pairAtom ρ U 2 1 + tailPart ρ U 2) + reward 2 (chi 2) (pairAtom ρ U 2 (-1)) =
          Real.sqrt ((eigDesc ρ 0 + eigDesc ρ 3) * (eigDesc ρ 1 + eigDesc ρ 2)) := by sorry

end Supplement

end SpectralFeedback
