-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_covariant_complement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.covariant_complement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:52:59.726194+00:00
-- url     : https://prove2.me/theorems/216ca455-7597-4ef2-b4a1-b318391eee87
-- title:
--   Covariant CP maps admit covariant complements
-- statement:
--   Let $G$ be a group, $U_A,U_B$ projective unitary actions on finite complex input/output spaces, and $\Phi$ a CP map with nonzero input satisfying $\Phi(U_A(g)XU_A(g)^*)=U_B(g)\Phi(X)U_B(g)^*$. There exist a finite environment, a projective unitary action $U_C$, and a common dilation $V$ with receiver $\Phi$ such that
--
--   $$VU_A(g)=(U_B(g)\otimes U_C(g))V,\qquad
--   \widetilde\Phi(U_A(g)XU_A(g)^*)=U_C(g)\widetilde\Phi(X)U_C(g)^*.$$
--
--   If $U_L(gh)=\mu_L(g,h)U_L(g)U_L(h)$, their modulus-one multipliers satisfy $\mu_B\mu_C=\mu_A$. The environment direction is fixed by the intertwiner, correcting the printed Kraus-row convention. This asserts existence of a covariant complementary representative.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 6, Covariant CP maps admit covariant complements

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

/-- PDF pp.6–7: a compatible covariant complementary REPRESENTATIVE.
Printed D-versus-adjoint direction is corrected by V U_A=(U_B tensor U_C)V.
The two projective multipliers need not coincide. -/
theorem covariant_complement [Nonempty A] {G : Type*} [Group G]
    (Phi : Superop A B) (hPhi : FiniteKrausCP Phi)
    (UA : ProjectiveAction G A) (UB : ProjectiveAction G B) (hcov : AllOperatorCovariant Phi UA UB) :
    ∃ (r : ℕ) (UC : ProjectiveAction G (Fin r)) (V : Matrix (B × Fin r) A ℂ),
      receiverChannel V = Phi ∧
      (∀ g h, UB.multiplier g h * UC.multiplier g h = UA.multiplier g h) ∧
      (∀ g, V * (UA.unitary g : Matrix A A ℂ) =
        ((UB.unitary g : Matrix B B ℂ) ⊗ₖ (UC.unitary g : Matrix (Fin r) (Fin r) ℂ)) * V) ∧
      AllOperatorCovariant (complementaryChannel V) UA UC := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
