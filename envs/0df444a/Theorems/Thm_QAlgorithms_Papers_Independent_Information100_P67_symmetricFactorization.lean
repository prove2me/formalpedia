-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_symmetricFactorization
-- name    : QAlgorithms.Papers.Independent.Information100.P67.symmetricFactorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:57:51.067238+00:00
-- url     : https://prove2.me/theorems/9f025f39-11d2-4df5-a0a3-a593ac2b6f7e
-- title:
--   Lemma 6.1 (Symmetric factorization)
-- statement:
--   Fix a finite-dimensional degradable channel with an isometric dilation $U:A\to BE$. Append an independent maximally mixed receiver qubit with its fixed Bell purification, giving $\widetilde U:A\to(B\otimes\mathbb C^2)(E\otimes\mathbb C^2)$. There are positive-dimensional $F,G$ and isometries $V:\widetilde B\to F\widetilde E$, $J:A\to FG$, and $W:G\to\widetilde E\widetilde E$ such that $V$ dilates a degrading channel and
--
--   $$(V\otimes I)\widetilde U=(I_F\otimes W)J,\qquad \mathrm{Swap}\,W=W,\qquad WW^\dagger=(I+\mathrm{Swap})/2.$$
--
--   Thus $W$ identifies $G$ isometrically with the entire symmetric tensor square. The appended qubit leaves $q_{\mathcal N}$ unchanged. Extending any original code by ignoring the receiver qubits preserves its validity, optimized joint fidelity, and actual-marginal joint fidelity exactly. This gives the symmetric-range construction and the precise code preservation asserted in Lemma 6.1; no maximal-error preservation clause is added.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 28, Lemma 6.1 (Symmetric factorization)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Lemma 6.1, PDF p.28 and Appendix A pp.39–42. W is an isometry
ONTO the swap-fixed subspace: WW†=(I+Swap)/2. J,W and the channel/code
extension are actual constructed witnesses, not equality-of-marginal surrogates. -/
theorem symmetricFactorization [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U) :
    let Uext := mixedQubitExtension U
    (∃ f g : ℕ, 0 < f ∧ 0 < g ∧
      ∃ V : Matrix (Fin f × (E × Bool)) (B × Bool) ℂ,
      ∃ J : Matrix (Fin f × Fin g) A ℂ,
      ∃ W : Matrix ((E × Bool) × (E × Bool)) (Fin g) ℂ,
        IsSymmetricFactorization Uext V ∧ IsIsometry J ∧ IsIsometry W ∧
        symmetricDilation Uext V = Matrix.kronecker (1 : Matrix (Fin f) (Fin f) ℂ) W * J ∧
        environmentSwap * W = W ∧
        W * Wᴴ = (1 / 2 : ℂ) • (1 + environmentSwap)) ∧
    maximumCoherentInformation Uext = maximumCoherentInformation U ∧
    (∀ n (code : PrivateCode A B n), code.Valid →
      (extendCode code).Valid ∧ optimizedFidelity Uext (extendCode code) = optimizedFidelity U code ∧
      marginalFidelity Uext (extendCode code) = marginalFidelity U code) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
