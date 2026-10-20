-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P01_embeddingCounterexample
-- name    : QAlgorithms.Papers.Independent.Frontier30.P01.embeddingCounterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:26:26.579821+00:00
-- url     : https://prove2.me/theorems/9ae243ad-4f56-4167-81d8-751f20b28b9f
-- title:
--   Positive-amplitude embedding can fail to preserve a perfect output key
-- statement:
--   Let all four registers $A,B,A',E$ be qubits. Write $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ and $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$, and define the unit vector
--
--   $$
--   |v\rangle=\frac1{\sqrt2}\bigl(|00\rangle_{AB}|+\rangle_{A'}|+\rangle_E+|11\rangle_{AB}|\Phi^+\rangle_{A'E}\bigr).
--   $$
--
--   All coefficients are nonnegative, so $|v\rangle$ is the positive-amplitude embedding of the distribution obtained by measuring every register in the computational basis. After that full measurement and disposal of $A'$, the resulting state is an ideal uniform correlated key bit independent of Eve, whose state is $I_E/2$. In contrast, disposing of $A'$ while leaving Eve quantum and measuring only $A,B$ yields
--
--   $$
--   \sigma_{ABE}=\frac12\left(|00\rangle\langle00|\otimes|+\rangle\langle+|+|11\rangle\langle11|\otimes\frac{I_E}{2}\right).
--   $$
--
--   There is no density matrix $\tau_E$ for which $\sigma_{ABE}=\frac12(|00\rangle\langle00|+|11\rangle\langle11|)\otimes\tau_E$. This example disproves preservation of a perfect output key by this operation; it makes no assertion that the optimal quantum key rate is zero.
--
--   **Formalization Note** Equation (39) omits the common normalization factor $1/\sqrt2$. It is restored to match the source's use of a state and its subsequent half-weighted mixture. Independent moderation of this correction remains pending.
-- source:
--   Unifying classical and quantum key distillation, arXiv:quant-ph/0608199v3, PDF p. 14, embedding-counterexample

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P01

namespace QAlgorithms.Papers.Independent.Frontier30.P01

open scoped Matrix ComplexConjugate

noncomputable section

/-- arXiv:quant-ph/0608199v3, PDF p.14, Eq.(39) and its following paragraph.
Source correction: include the omitted common 1/sqrt(2), since the printed
vector has squared norm two and the source's output has weights 1/2.
This is a protocol-wise failure of perfect secrecy, not a claim of zero KD. -/
theorem embeddingCounterexample :
    ‖counterVector‖ = 1 ∧
    qqqVector (fun x => Complex.normSq (counterVector x)) = counterVector ∧
    traceLeft (Information100.P34.dephasing (pureDensity counterVector)) =
      Dependency50.P24.idealCCQ ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    measureAB (traceLeft (pureDensity counterVector)) =
      (1/2 : ℂ) • Matrix.kronecker (pureDensity (ket (0,0))) (pureDensity plusVector) +
      (1/2 : ℂ) • Matrix.kronecker (pureDensity (ket (1,1)))
        ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    ¬ (∃ tau : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix tau ∧
      measureAB (traceLeft (pureDensity counterVector)) = Dependency50.P24.idealCCQ tau) := by sorry

end

end QAlgorithms.Papers.Independent.Frontier30.P01
