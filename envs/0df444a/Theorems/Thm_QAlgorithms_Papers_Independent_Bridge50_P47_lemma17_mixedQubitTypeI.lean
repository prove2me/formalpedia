-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_lemma17_mixedQubitTypeI
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.lemma17_mixedQubitTypeI
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:50:28.364612+00:00
-- url     : https://prove2.me/theorems/12324075-7b6b-4a3e-9c27-abf9afa85026
-- title:
--   Lemma 17: mixed-qubit extension is type I
-- statement:
--   Let $\mathcal N:\mathcal L(A')\to\mathcal L(B)$ be degradable on nonzero finite quantum systems. Let $B_0$ be a qubit and $\tau_{B_0}=I_2/2$. The channel
--
--   $$
--   \widetilde{\mathcal N}(\rho)=\mathcal N(\rho)\otimes\tau_{B_0}
--   $$
--
--   is degradable of type I: it has a Stinespring isometry $\widetilde U$ and an isometric dilation $\widetilde V$ of a genuine degrading map for which $I_F\otimes\operatorname{SWAP}$ acts on $\widetilde V\widetilde U$ by a global sign; indeed, the degrading dilation can be chosen with the plus sign. The chosen extension uses the standard Bell purification of the mixed output qubit. The extra system is an independent output ancilla; this construction converts any degradable channel into a type-I one.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 10, Lemma 17: mixed-qubit extension is type I

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Lemma 17, PDF pp.10–11: append an independent mixed OUTPUT qubit.
The VU correction to Definition 16's ill-typed UV is used throughout. -/
theorem lemma17_mixedQubitTypeI [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : P67.IsDegradable U) :
    IsTypeI (P67.mixedQubitExtension U) ∧
    (∃ f : ℕ, 0 < f ∧ ∃ V : Matrix (Fin f × (E × Bool)) (B × Bool) ℂ,
      IsTypeIFactorization (P67.mixedQubitExtension U) V false) ∧
    (∀ rho : Matrix A A ℂ,
      P67.receiverChannel (P67.mixedQubitExtension U) rho =
        Matrix.kronecker (P67.receiverChannel U rho)
          ((1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
