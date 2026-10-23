-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P11_exampleCorrelated
-- name    : QAlgorithms.Papers.Independent.Gap20.P11.exampleCorrelated
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:19:09.250752+00:00
-- url     : https://prove2.me/theorems/a2b6da9c-6c76-478f-878d-5be443f98db5
-- title:
--   One classical bit merges the coherent classical-correlation example
-- statement:
--   Consider the normalized purification
--
--   $$
--   |\psi\rangle_{RAB}=\frac{|000\rangle+|111\rangle}{\sqrt2},\qquad
--   \rho_{AB}=\frac{|00\rangle\langle00|+|11\rangle\langle11|}{2}.
--   $$
--
--   Its conditional entropy is $S(A\mid B)=0$. Alice measures in the normalized basis $(|0\rangle\pm|1\rangle)/\sqrt2$ and sends the outcome $s\in\{0,1\}$ as one classical bit. Bob applies the conditional isometry $|b\rangle\mapsto(-1)^{sb}|b\rangle_{A'}|b\rangle_B$, with $A'$ a local ancilla. The measurement is complete, each decoder is a quantum channel, and the resulting density operator is exactly
--
--   $$
--   |\psi\rangle\langle\psi|_{RA'B},
--   $$
--
--   with Alice's remaining register trivial. No quantum message or initial shared resource is used. This recovers the coherent purification against $R$, rather than merely recovering the diagonal density $\rho_{AB}$.
-- source:
--   Quantum information can be negative, arXiv:quant-ph/0505062v1, PDF p. 4, Example 2: coherent classical correlation can be merged with zero quantum messages

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P11

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, example 2: S(A|B)=0 and the explicit plus/minus protocol recovers
all coherences with R, not merely the diagonal mixed marginal rho_AB. -/
theorem exampleCorrelated :
    IsState correlatedPurification ∧
    conditionalEntropy (traceLeft (pureDensity correlatedPurification)) = 0 ∧
    IsKrausFamily plusMinusRow ∧
    (∀ s, IsChannel (conjSuperop (correlatedDecoder s))) ∧
    idTensorSuperop correlatedOperation (pureDensity correlatedPurification) =
      pureDensity correlatedTarget := by sorry

end QAlgorithms.Papers.Independent.Gap20.P11

end
