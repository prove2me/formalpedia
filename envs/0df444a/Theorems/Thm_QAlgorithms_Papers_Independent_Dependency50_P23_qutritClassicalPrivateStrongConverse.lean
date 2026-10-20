-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_qutritClassicalPrivateStrongConverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.qutritClassicalPrivateStrongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:48:10.891137+00:00
-- url     : https://prove2.me/theorems/53255537-732b-48fc-b003-c9c4c16a7d00
-- title:
--   Unnumbered main conclusion: classical and private strong converse for N_α
-- statement:
--   Let $0<\alpha\le\pi/4$, and let $\mathcal N_\alpha$ be the qutrit channel with the two Kraus operators of §V.C. Its classical and private capacities are both one bit. For every $r>1$ there exist $c>0$ and $n_0\ge1$ such that every $n\ge n_0$ and integer $M\ge1$ with $\log_2M\ge nr$ satisfy
--
--   $$p_{\mathrm{success}}\le2^{-cn}$$
--
--   for every unassisted $M$-message collective code on $\mathcal N_\alpha^{\otimes n}$, and for the decoding success of every valid private-code data set with $M$ messages. The same constants apply to all these codes, independently of secrecy quality. Thus the conclusion concerns loss of reliable communication, not merely loss of privacy.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 20, Unnumbered main conclusion

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

/-- PDF pp.19–20, unnumbered main conclusion: success of EVERY unassisted
classical code, hence every private code, decays exponentially above one bit.
No secrecy premise is imposed to obtain the reliability bound. -/
theorem qutritClassicalPrivateStrongConverse (alpha : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    ordinaryClassicalCapacity (qutrit alpha) = 1 ∧ (QAlgorithms.Papers.Independent.Information100.P67.privateCapacity
      .uniformOptimized (qutritDilation alpha)) = 1 ∧
    ∀ r : ℝ, 1 < r → ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∀ M : ℕ, 0 < M → (n : ℝ)*r ≤ log2 M →
        (∀ K : UACode (Fin n → Fin 3) (Fin n → Fin 3) M,
          uaCodeSuccess (piSuperop (fun _ : Fin n => qutrit alpha)) K ≤
            Real.rpow 2 (-c*n)) ∧
        (∀ K : QAlgorithms.Papers.Independent.Information100.P67.PrivateCode
            (Fin 3) (Fin 3) n, K.Valid → K.M = M →
          (M : ℝ)⁻¹ * ∑ k : Fin K.M,
            effectProb (K.measurement k)
              (piSuperop (fun _ : Fin n => qutrit alpha) (K.messages k)) ≤
            Real.rpow 2 (-c*n)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
