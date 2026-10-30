-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_memoryless_code_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.memoryless_code_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:29:30.227674+00:00
-- url     : https://prove2.me/theorems/1d7e93cc-9f4c-440a-b5a9-66e97990f875
-- title:
--   Unnumbered (82)–(86): memoryless bounds and regularized achievability
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   For each positive block length $n$, positive integers $M,L$, and auxiliary law $P_L$, there is one $\lceil M/4\rceil$-message code on the physical memoryless channel using only $P_L$, with
--   $$\begin{aligned}
--   \epsilon_{\max}&\le48\inf_{0\le t\le1}(ML)^te^{-ntI_{-t}(W_B,P_X)},\\
--   I_{\max}&\le12v_n\inf_{0<s\le1}\frac{e^{-sH_{1+s}(P_L)+nsI_s(W_E,P_X)}}s,\\
--   d_{1,\max}&\le24\inf_{0<s\le1}\mu_{s,n}e^{\frac s2(nI_s^G(W_E,P_X)-H_{1+s}(P_L))}.
--   \end{aligned}$$
--   Here $v_n= v(\bar W_{P_X}^{\otimes n})$ and $\mu_{s,n}=\min\{4+\sqrt{v(A_s^{\otimes n})},(4+\sqrt{\lceil n\lambda_s\rceil})e^{s/2}\}$. If a positive semidefinite matrix has at most $d\ge1$ distinct eigenvalues, its $n$-fold power has at most $\binom{n+d-1}{d-1}$; supported spectral spread of a density matrix scales by $n$.
--
--   For auxiliary sequences with $\log M_n/n\to R\ge0$, $\log L_n/n\to R_{\rm aux}$, $R+R_{\rm aux}<I(W_B,P_X)$ and $\liminf H_{1+s}(P_{L_n})/n>I_s(W_E,P_X)$ for some fixed $0<s\le1$, such codes have rate $R$, vanishing average error, and vanishing source-universal leakage. Finally, writing $B_n$ for the supremum of $I(V;B^n)-I(V;E^n)$ over every finite auxiliary law and stochastic preprocessing into $X^n$,
--   $$\lim_{n\to\infty}B_n/n\text{ exists},\qquad C_{W_B,W_E}\ge\lim_{n\to\infty}B_n/n.$$
--   Capacity optimizes unrestricted stochastic encoders; it is not defined relative to a fixed weak auxiliary source.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 13, Unnumbered (82)–(86): memoryless bounds and regularized achievability

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

/-- PDF p.13, (82)–(86): memoryless expurgated bounds and unrestricted regularized
achievability. Corrections: ceil(M/4), exp(-n t I_-t), and the spectral type count
binomial(n+d-1,d-1), replacing the false printed (dim E-1)^(n+1).
The coarser printed factor v_n in (83) is retained. -/
theorem memoryless_code_bounds [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE) (PX : X → ℝ) (hPX : IsLaw PX) :
    (∀ (n M L : ℕ), 0 < n → 0 < M → 0 < L → ∀ PL : Fin L → ℝ, IsLaw PL →
      ∃ C : WiretapCode (Fin n → X) (Fin n → B) ((M + 3) / 4), UsesLaw PL C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, maxError (productOutput n WB) C ≤
        48 * Real.rpow (M * L : ℕ) t * Real.exp (-(n : ℝ) * t * petzInfo (-t) WB PX)) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, Imax (hayashiCompose (productOutput n WE) C.encoder) ≤
        12 * eigenCount (matrixTensor n (average WE PX)) / s *
          Real.exp (-s * hayashiRenyiEntropy s PL + n * s * petzInfo s WE PX)) ∧
      (∀ s ∈ Set.Ioc (0 : ℝ) 1, d1max (hayashiCompose (productOutput n WE) C.encoder) ≤
        24 * blockMu n s WE PX * Real.exp (s / 2 * ((n : ℝ) * gallagerInfo s WE PX - hayashiRenyiEntropy s PL)))) ∧
    (∀ (sigma : Matrix E E ℂ), sigma.PosSemidef → ∀ (d : ℕ), 0 < d → eigenCount sigma ≤ d →
      ∀ n : ℕ, eigenCount (matrixTensor n sigma) ≤ Nat.choose (n + d - 1) (d - 1)) ∧
    (∀ sigma : Matrix E E ℂ, IsDensityMatrix sigma → ∀ n : ℕ,
      spectralSpread (matrixTensor n sigma) = n * spectralSpread sigma) ∧
    (∀ (M L : ℕ → ℕ), (∀ n, 0 < M n) → (∀ n, 0 < L n) →
      ∀ (PL : (n : ℕ) → Fin (L n) → ℝ), (∀ n, IsLaw (PL n)) →
      ∀ R Raux : ℝ, 0 ≤ R →
      Tendsto (fun n => Real.log (M n) / n) atTop (nhds R) →
      Tendsto (fun n => Real.log (L n) / n) atTop (nhds Raux) →
      R + Raux < holevo PX WB →
      (∃ s ∈ Set.Ioc (0 : ℝ) 1,
        (petzInfo s WE PX : EReal) <
          Filter.liminf (fun n => (hayashiRenyiEntropy s (PL n) / n : EReal)) atTop) →
      ∃ S : CodeSequence X B, (∀ n, S.size n = (M n + 3) / 4) ∧
        (∀ n, UsesLaw (PL n) (S.code n)) ∧ ReliableRate WB R S ∧
        Tendsto (fun n => Imax (hayashiCompose (productOutput n WE) (S.code n).encoder)) atTop (nhds 0)) ∧
    (∃ a : ℝ,
      Tendsto (fun n => QAlgorithms.Papers.Independent.Information100.P56.blockPrivate n WB WE / n)
        atTop (nhds a) ∧ (a : EReal) ≤ wiretapCapacity WB WE) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
