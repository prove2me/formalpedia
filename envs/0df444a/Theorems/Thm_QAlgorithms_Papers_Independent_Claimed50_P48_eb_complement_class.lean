-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_eb_complement_class
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.eb_complement_class
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:43:35.186197+00:00
-- url     : https://prove2.me/theorems/5a7d22e4-7c30-40b5-842d-1d1b40af3abd
-- title:
--   Equations (13)–(15): characterization of complements of entanglement-breaking CP maps
-- statement:
--   For arbitrary finite vectors $\psi_\alpha\in H_A$ and $\varphi_\alpha\in H_B$, with $H_A\ne0$, let $\Phi$ be their rank-one Kraus map. Put $c_{\alpha\beta}=\langle\varphi_\beta|\varphi_\alpha\rangle$. Then $c$ is positive semidefinite and a complement is
--
--   $$T_{c,\psi}(X)_{\alpha\beta}=c_{\alpha\beta}\langle\psi_\alpha|X|\psi_\beta\rangle.$$
--
--   Conversely every positive semidefinite $c$ has that Gram form, with output vectors in the coordinate space indexed by $\alpha$, and yields such a complement. If $c=vv^*$, then $T_{c,\psi}(X)=\sum_j L_jXL_j^*$ with $(L_j)_{\alpha i}=v_{\alpha j}\overline{\psi_\alpha(i)}$. A CP map belongs to the class of complements of entanglement-breaking maps exactly when it is equivalent, by the two identities (2), to some $T_{c,\psi}$. No basis condition is imposed on $\psi$. This characterizes the full class (14).
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 4, Equations (13)–(15): characterization of complements of entanglement-breaking CP maps

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

/-- Equations (13)–(15), PDF pp.4–5: arbitrary vectors, the converse Gram
construction, Kraus formula, and ALL complements up to (2). -/
theorem eb_complement_class [Nonempty A]
    (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    (gram phi).PosSemidef ∧
    CPComplementary (krausApply (rankOneKraus psi phi)) (arbitraryVectorComplement (gram phi) psi) ∧
    (∀ c : Matrix K K ℂ, c.PosSemidef → ∃ phi2 : K → EuclideanSpace ℂ K, gram phi2 = c ∧
      CPComplementary (krausApply (rankOneKraus psi phi2)) (arbitraryVectorComplement c psi)) ∧
    (∀ v : Matrix K B ℂ, arbitraryVectorComplement (v * vᴴ) psi = krausApply (gramKraus v psi)) ∧
    (∀ Phi : Superop A C, EBComplement Phi ↔
      ∃ (r : ℕ) (c : Matrix (Fin r) (Fin r) ℂ) (psi2 : Fin r → EuclideanSpace ℂ A),
        c.PosSemidef ∧ Equivalent (arbitraryVectorComplement c psi2) Phi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
