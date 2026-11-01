-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_channelSimulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.channelSimulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:09:06.345181+00:00
-- url     : https://prove2.me/theorems/97578cfb-c671-4f8f-ad6b-41c09063a975
-- title:
--   Theorem 3.1: channel simulation with quantum side information
-- statement:
--   Let $X$ be a finite nonempty alphabet, $B$ a finite nonzero quantum register, and $\{p(x),\rho_x^B\}$ a normalized classical–quantum source. Every $\rho_x^B$ is a density operator, including when $p(x)=0$. Let $W(y\mid x)$ be a stochastic channel on a finite nonempty output alphabet $Y$. All information quantities below are in bits in the state $\rho^{XYB}=\sum_{x,y}p(x)W(y\mid x)|x,y\rangle\langle x,y|\otimes\rho_x^B$.
--
--   For nonnegative rates $R,C$, a pair is achievable exactly when
--   $$R\ge I(X;Y)-I(Y;B),\qquad R+C\ge H(Y\mid B).$$
--   Achievability means that for every error $\epsilon>0$ and rate slack $\delta>0$, every sufficiently large positive blocklength $n$ admits a code with at most $n(R+\delta)$ forward classical bits and $n(C+\delta)$ independent uniform shared bits. Alice uses private stochastic encoding, Bob uses a coin/message-controlled POVM with its square-root instrument, and both retain their output $Y^n$. The full trace-norm error on the original $X^n$, both output copies, and postmeasurement $B^n$ is at most $\epsilon$, with no factor $1/2$.
--
--   This gives the complete source-relative classical communication–common randomness trade-off while preserving quantum side information.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 5, Theorem 3.1: channel simulation with quantum side information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.5, Theorem 3.1: exact rate region, with preservation of Bob's quantum
source and both feedback outputs. All information is computed in Eq.(2). -/
theorem channelSimulation {X B : Type} [Fintype X] [Fintype B]
    [Nonempty X] [Nonempty B] (E : CQData X B) (hE : E.Valid)
    (V : Auxiliary X) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    SimulationAchievable E V R C ↔
      auxCost E V ≤ R ∧ shannon (auxProb E V) - auxIQ E V ≤ R + C := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
