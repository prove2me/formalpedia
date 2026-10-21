-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_kraus_complement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.kraus_complement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:41:49.208781+00:00
-- url     : https://prove2.me/theorems/85d43912-a670-40fc-8d1f-bd258e8d5a68
-- title:
--   Equations (10)–(12): explicit complementary Kraus construction
-- statement:
--   Let $K_\alpha:H_A\to H_B$ be any finite Kraus family with $H_A\ne0$, without normalization. Its common dilation has entries $V_{(j,\alpha),i}=(K_\alpha)_{j,i}$. The receiver is $\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^*$, and the complementary map is
--
--   $$\widetilde\Phi(X)_{\alpha\beta}=\operatorname{Tr}(K_\alpha X K_\beta^*)
--   =\operatorname{Tr}(XK_\beta^*K_\alpha).$$
--
--   Define $L_j$ by $(L_j)_{\alpha i}=(K_\alpha)_{ji}$. Then $\widetilde\Phi(X)=\sum_jL_jXL_j^*$ for every operator $X$. Applying the row construction twice returns the original Kraus family, so its double complement returns $\Phi$ in these coordinate bases. This gives the explicit construction (10)–(12).
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 4, Equations (10)–(12): explicit complementary Kraus construction

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- Equations (10)–(12), PDF p.4: correct alpha,beta trace order and the
computed output-row Kraus family. Twice reshuffling returns the original map. -/
theorem kraus_complement [Nonempty A] (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E ∧
    (∀ rho a b, complementaryChannel (indexedKrausDilation E) rho a b = (E a * rho * (E b)ᴴ).trace ∧
      complementaryChannel (indexedKrausDilation E) rho a b = (rho * (E b)ᴴ * E a).trace) ∧
    complementaryChannel (indexedKrausDilation E) = krausApply (rowKraus E) ∧
    rowKraus (rowKraus E) = E ∧
    complementaryChannel (indexedKrausDilation (rowKraus E)) = krausApply E := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
