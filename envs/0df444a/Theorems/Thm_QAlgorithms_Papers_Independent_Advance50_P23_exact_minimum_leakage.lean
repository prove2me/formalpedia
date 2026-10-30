-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_exact_minimum_leakage
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.exact_minimum_leakage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:34:12.285377+00:00
-- url     : https://prove2.me/theorems/9d286172-7189-4469-a2d6-75b03a0e2d15
-- title:
--   Theorem 3, (102): exact minimum leakage rate
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   Let $C_{W_B,W_E}$ be the operational private capacity over unrestricted stochastic codes, $C_B=\max_P I(W_B,P)$ the receiver capacity, and $0\le R\le C_B$ with $R>C_{W_B,W_E}$. Let $\mathcal I(R)$ be the infimum of normalized-leakage limits over reliable code sequences of rate $R$. For block length $n$, optimize $[I(V;B^n)-I(V;E^n)]/n$ over every finite auxiliary and stochastic preprocessing into $X^n$ subject to $I(V;B^n)\ge nR$, and call its limit $H(R)$. Then that limit exists and
--   $$\mathcal I(R)=R-H(R).$$
--   The operational infimum is not assumed attained. Extended-real infima and suprema preserve infeasibility rather than returning zero on empty sets.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 17, Theorem 3, (102): exact minimum leakage rate

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF pp.16–19, Theorem 3, (100),(102): exact minimum leakage above private
capacity, within receiver feasibility. Optimizations use all finite stochastic
auxiliaries. No single code sequence is assumed to attain the infimum. -/
theorem exact_minimum_leakage [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE)
    (R : ℝ) (hR : 0 ≤ R) (habove : wiretapCapacity WB WE < (R : EReal))
    (hfeasible : R ≤ receiverCapacity WB) :
    leakedRate WB WE R = (R : EReal) - equivocationFunction R WB WE ∧
    Tendsto (fun n => constrainedPrivate n R WB WE) atTop (nhds (equivocationFunction R WB WE)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
