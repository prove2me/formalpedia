-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_localUnital_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.localUnital_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:15:54.661088+00:00
-- url     : https://prove2.me/theorems/2cf141d2-033c-47bc-b65a-b237fe37c15a
-- title:
--   Remark II.4: converse for local unital channels
-- statement:
--   Let $\rho_{AB}$ be a density matrix on finite nonzero spaces, put $d=d_Ad_B$, and fix $n\ge1$, $\epsilon\ge0$. Let $F$ and $G$ be local CPTP maps on $A^{\otimes n}$ and $B^{\otimes n}$, respectively, with $F(\mathbf1)=\mathbf1$ and $G(\mathbf1)=\mathbf1$. If their product channel $T=F\otimes G$ has output within full trace norm $\epsilon$ of a normalized product state, then
--
--   $$S_e(T,\rho^{\otimes n})\ge n\bigl(I(A:B)_\rho-3\epsilon\log_2d-\eta(3\epsilon)\bigr).$$
--
--   The capped function $\eta$ is as in Proposition II.1. This extends the entropy-exchange converse to compositions of local unital channels.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 5, Remark II.4: converse for local unital channels

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Remark II.4: literal identity-preserving local CPTP maps. -/
theorem localUnital_converse {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (n : ℕ) (hn : 0 < n) (eps : ℝ) (heps : 0 ≤ eps)
    (F : Superop (Copies A n) (Copies A n)) (G : Superop (Copies B n) (Copies B n))
    (hF : IsChannel F) (hG : IsChannel G) (hF1 : F 1 = 1) (hG1 : G 1 = 1)
    (hdec : Decorrelates (localProduct F G (sourcePower rho n)) eps) :
    (n : ℝ) * (mutualInformation rho - 3*eps*logDimension A B - erasureEta (3*eps)) ≤
      entropyExchange (localProduct F G) (sourcePower rho n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
