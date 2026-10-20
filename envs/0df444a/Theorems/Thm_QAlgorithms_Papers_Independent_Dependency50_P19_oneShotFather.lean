-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_oneShotFather
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.oneShotFather
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:14:39.170868+00:00
-- url     : https://prove2.me/theorems/01c3ccbe-2437-46c5-8842-f656d64029e8
-- title:
--   One-shot father with a channel-derived source
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $N:A\to BE$ be a Stinespring isometry and $W_1:A_0A_3\to A$ an isometry, with $k=d_{A_0}>0$ and $m=d_{A_3}>0$. Construct $\psi=(I\otimes NW_1)(\Phi_k^{RA_0}\otimes\Phi_m^{B_3A_3})(I\otimes NW_1)^\dagger$. There exist an isometric encoder $W_2:A_0A_3\to A$ and a decoder $V:B_3B\to H\widetilde B$, where $H$ is a full copy of $RB_3B$ and $\widetilde B$ a copy of $A_0$, such that
--
--   $$
--   \left\|\rho_{\rm out}^{REH\widetilde B}-\psi^{EH}\otimes\Phi_k^{R\widetilde B}\right\|_1
--   \le 2\left[\frac{2km\,d_E}{m^2}\left(\operatorname{Tr}[(\psi^B)^2]+\frac{2}{km}\operatorname{Tr}[(\psi^E)^2]\right)\right]^{1/4}.
--   $$
--
--   Here $\rho_{\rm out}$ is produced from the actual two EPR pairs by $W_2$, $N$, and $V$, without acting on $R$ or discarding $E$. The residual target $\psi^{EH}$ is the original channel-derived pure state with registers relabelled. The encoder has the form $W_2=W_1T$ for a unitary $T$ on $A_0A_3$, as supplied by the transpose construction. The consumed assistance is $\log_2 m$ ebits and transmitted entanglement is $\log_2 k$.
--
--   This is one-use entanglement transmission on the specified EPR input.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 10, Section V, Eqs. (31)–(32)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section V, PDF p.10, Eqs.(31)–(32): one-use entanglement transmission.
The state determining the two purities is constructed from N and W1. -/
theorem oneShotFather {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    [Nonempty A] [Nonempty B] [Nonempty E]
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (N : Matrix (B × E) A ℂ) (hN : IsIso N)
    (W1 : Matrix A (Fin k × Fin m) ℂ) (hW1 : IsIso W1) :
    ∃ W2 : Matrix A (Fin k × Fin m) ℂ, IsIso W2 ∧
    ∃ T : Matrix.unitaryGroup (Fin k × Fin m) ℂ, W2 = W1 * (T : Matrix _ _ ℂ) ∧
    ∃ V : Matrix ((((Fin k × Fin m) × B)) × Fin k) (Fin m × B) ℂ,
      IsIso V ∧
      traceNorm (fatherOneShotOutput N W2 V - fatherOneShotTarget k
        (fatherResidual k m (fatherSource k m N W1))) ≤
      2 * Real.rpow
        ((2 * ((k*m : ℕ) : ℝ) * Fintype.card E / (m : ℝ)^2) *
          (purity (traceRight (traceLeft (fatherSource k m N W1))) +
           (2 / ((k*m : ℕ) : ℝ)) *
             purity (traceLeft (traceLeft (fatherSource k m N W1))))) (1/4 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
