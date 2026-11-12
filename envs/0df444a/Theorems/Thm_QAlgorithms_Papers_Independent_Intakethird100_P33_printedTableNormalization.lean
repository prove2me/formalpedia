-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P33_printedTableNormalization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P33.printedTableNormalization
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T06:53:45.517886+00:00
-- url     : https://prove2.me/theorems/60ce65b4-2888-4648-9ea5-355fdc857688
-- title:
--   Endnote [6]: normalization of the printed nondecoy monitoring count table
-- statement:
--   Let $x,p_d,f\in\mathbb R$. In the source's printed first-order nondecoy table, give each pattern 00, 01, 10, 11 weight $(1-f)/4$. Its two signal coefficients are $(x/4,x/4)$, $(0,0)$, $(x,0)$, and $(x/4,x/4)$, respectively. For a signal coefficient $s$, the specified table count is $s+(1-s)p_d$. If $C_{a,r}$ is that count multiplied by the printed pattern weight, then
--
--   $$
--   \sum_{a\in\{00,01,10,11\}}\sum_{r=1}^2 C_{a,r}
--   =\left[{x\over2}+\left(2-{x\over2}\right)p_d\right](1-f).
--   $$
--
--   The identity holds for all real parameters. It checks the algebra of endnote [6], without equating the table to exact coherent click probabilities or resolving the sampling convention in (12). A probability interpretation of individual first-order entries would need additional parameter-domain and detector assumptions.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, PDF p. 7, Endnote [6], with (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P33

open scoped BigOperators ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity rankOne)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P48 (vacuumAmplitude)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P34
  (TwoModeFock fockKet photonMean)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (coherentPair coherentPairCoefficients)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.4,7, (13) and endnote [6]: algebraic sum of the printed eight entries.
The statement does not interpret the table weights as an exact sampling law.
No domain guards are needed for a polynomial identity over the reals. -/
theorem printedTableNormalization (x pd f : ℝ) :
    (∑ pattern : Fin 4, ∑ port : Fin 2, printedCount x pd f pattern port) =
      (x / 2 + (2 - x / 2) * pd) * (1 - f) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P33

end
