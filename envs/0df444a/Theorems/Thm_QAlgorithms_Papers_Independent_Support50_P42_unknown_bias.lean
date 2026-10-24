-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_unknown_bias
-- name    : QAlgorithms.Papers.Independent.Support50.P42.unknown_bias
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:18:58.89211+00:00
-- url     : https://prove2.me/theorems/b2e99e2b-69ba-4883-b528-3e2deedb6e9e
-- title:
--   Schmidt projection does not require the common bias
-- statement:
--   For every batch size $n\ge0$ and a fixed known local Schmidt basis, there is one complete measurement $\{P_k\}_{k=0}^n$ chosen before the common bias $p\in[0,1]$. Here $P_k$ is the projector onto strings of weight $k$. For all biases,
--
--   $$\Pr(K=k)=\binom nk(1-p)^{n-k}p^k,\qquad |\psi_k\rangle=\binom nk^{-1/2}\sum_{|x|=k}|x,x\rangle$$
--
--   whenever that outcome has positive probability. Thus the successful conditional state and the measurement are independent of the unknown common bias. This expresses the source's operational contrast with its bias-dependent Procrustean construction, without asserting an impossibility theorem for every other filter.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 9, §III: Schmidt projection is independent of the common unknown bias

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.9: one complete local measurement before every unknown common bias,
in a fixed known Schmidt basis. No blanket filter impossibility is asserted. -/
theorem unknown_bias (n : ℕ) :
    ∃ A : Fin (n+1) → Op (Fin n → Bool), IsKrausFamily A ∧
      A=(fun k => schmidtTypeProjector n k.val) ∧ ∀ p : ℝ, 0≤p → p≤1 → ∀ k : Fin (n+1),
        ‖act (Matrix.kronecker (A k) (1 : Op (Fin n → Bool))) (schmidtBlock n p)‖^2=
          schmidtOutcomeWeight n p k.val ∧
        (0<schmidtOutcomeWeight n p k.val →
          ((Real.sqrt (schmidtOutcomeWeight n p k.val))⁻¹ : ℂ) •
            act (Matrix.kronecker (A k) (1 : Op (Fin n → Bool))) (schmidtBlock n p)=typeState n k.val) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
