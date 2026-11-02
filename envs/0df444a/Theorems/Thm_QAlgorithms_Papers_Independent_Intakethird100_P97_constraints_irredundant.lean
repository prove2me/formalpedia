-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P97_constraints_irredundant
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P97.constraints_irredundant
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:38:36.031035+00:00
-- url     : https://prove2.me/theorems/fffc43b8-7c99-4943-a3c2-1edff8ad1672
-- title:
--   Remark 3: no proper subset of the three constraints suffices
-- statement:
--   Let $\rho_{ABCD}$ be a positive semidefinite complex density matrix of trace one on four finite-dimensional tensor factors $A,B,C,D$, each of positive dimension (dimension one is allowed). Every $S(X)$ is the base-two von Neumann entropy of the actual $X$ marginal of this same state, with $0\log_2 0=0$. For disjoint groups write $S(X\mid Y)=S(XY)-S(Y)$, $I(X;Y)=S(X)+S(Y)-S(XY)$, and $I(X;Z\mid Y)=S(XY)+S(YZ)-S(XYZ)-S(Y)$. Number the constraints $c_0=I(A;C\mid B)$, $c_1=I(B;C\mid A)$, and $c_2=I(A;B\mid D)$. For every proper subset $T\subsetneq\{0,1,2\}$ there is such a state satisfying
--
--   $$
--    c_i=0\quad(i\in T),\qquad I(C;D)<I(C;AB).
--   $$
--
--   Thus every one of the three constraints is necessary for this implication. The printed second counterexample has three-bit kets on $BC$; the intended two-party kets are $|00\rangle$ and $|11\rangle$.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, PDF p. 5, Remark 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "A" => ({0} : Finset (Fin 4))

local notation "B" => ({1} : Finset (Fin 4))

local notation "C" => ({2} : Finset (Fin 4))

local notation "D" => ({3} : Finset (Fin 4))

/-- PDF p.5, Remark 3: every proper subset of the three constraints admits a
counterexample to the conclusion. Source correction: the printed second witness
has three-bit kets on BC; these must read |00> and |11> on that two-party register.
The theorem states irredundance itself and does not assume witness MI values. -/
theorem constraints_irredundant :
    ∀ t : Finset (Fin 3), t ≠ Finset.univ →
      ∃ q : FourPartyState, (∀ i ∈ t, constraintValue (fourPartyEntropyBits q) i = 0) ∧
        mutualValue (fourPartyEntropyBits q) C D < mutualValue (fourPartyEntropyBits q) C (A ∪ B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P97

end
