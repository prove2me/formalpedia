-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_asymptotic_equivocation
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.asymptotic_equivocation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:33:12.121193+00:00
-- url     : https://prove2.me/theorems/402698ec-d841-4c8f-b27b-b928e5b2752a
-- title:
--   Unnumbered (96)–(99): auxiliary-randomness leakage rate
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   For every positive $n,M,L$, law $P_L$ and fixed $0<s\le1$, an $M$-message physical block code using that law obeys
--   $$\epsilon\le8\inf_{0\le t\le1}(ML)^te^{-ntI_{-t}(W_B,P_X)},$$
--   $$\frac{I_{\rm mix}}n\le\frac{\log v_n}n+\frac{\log4+[nsI_s(W_E,P_X)-sH_{1+s}(P_L)]_+}{ns}.$$
--   For arbitrary positive size sequences and auxiliary laws with $H_{1+s}(P_{L_n})/n\to R_0$, one can select codes using those laws with
--   $$\limsup_n I_{\rm mix}/n\le[I_s(W_E,P_X)-R_0]_+.$$
--   If that entropy-rate limit holds for every fixed $0<s\le1$ with the same $R_0$, a diagonal choice yields the bound $[I(W_E,P_X)-R_0]_+$ instead. No existence of an ordinary leakage limit is asserted. Let $\mathcal I(R)$ be the infimum of existing normalized-leakage limits over unrestricted reliable code sequences of rate $R$. In the regime $0\le R$, $C_{W_B,W_E}<R\le I(W_B,P_X)$,
--   $$\mathcal I(R)\le R-[I(W_B,P_X)-I(W_E,P_X)].$$
--   The printed square-root block backoff claim is not used to justify reliability.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 16, Unnumbered (96)–(99): auxiliary-randomness leakage rate

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

/-- PDF p.16, (96)–(99): finite-block and asymptotic leakage-rate bounds. The
positive part from (97) is kept; limit upper bounds are stated as limsup. A fixed-s
code sequence is selected only after s is fixed. The operational (99) is restricted
to the above-private-capacity and receiver-feasible regime of Section V. The specific
sqrt(n) boundary-hayashiReliability claim is deferred, not used as an extra hypothesis. -/
theorem asymptotic_equivocation [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE) (PX : X → ℝ) (hPX : IsLaw PX) :
    (∀ (n M L : ℕ), 0 < n → 0 < M → 0 < L → ∀ PL : Fin L → ℝ, IsLaw PL →
      ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      ∃ C : WiretapCode (Fin n → X) (Fin n → B) M, UsesLaw PL C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, hayashiCodeError (productOutput n WB) C ≤
        8 * Real.rpow (M * L : ℕ) t * Real.exp (-(n : ℝ) * t * petzInfo (-t) WB PX)) ∧
      Imix (hayashiCompose (productOutput n WE) C.encoder) / n ≤
        Real.log (eigenCount (matrixTensor n (average WE PX))) / n +
        (Real.log 4 + max (n * s * petzInfo s WE PX - s * hayashiRenyiEntropy s PL) 0) / (n * s)) ∧
    (∀ (M L : ℕ → ℕ), (∀ n, 0 < M n) → (∀ n, 0 < L n) →
      ∀ (PL : (n : ℕ) → Fin (L n) → ℝ), (∀ n, IsLaw (PL n)) →
      ∀ s ∈ Set.Ioc (0 : ℝ) 1, ∀ R0 : ℝ,
      Tendsto (fun n => hayashiRenyiEntropy s (PL n) / n) atTop (nhds R0) →
      ∃ S : CodeSequence X B, S.size = M ∧ (∀ n, UsesLaw (PL n) (S.code n)) ∧
        Filter.limsup (fun n => (Imix (hayashiCompose (productOutput n WE) (S.code n).encoder) / n : EReal))
          atTop ≤ (max (petzInfo s WE PX - R0) 0 : EReal)) ∧
    (∀ (M L : ℕ → ℕ), (∀ n, 0 < M n) → (∀ n, 0 < L n) →
      ∀ (PL : (n : ℕ) → Fin (L n) → ℝ), (∀ n, IsLaw (PL n)) → ∀ R0 : ℝ,
      (∀ s ∈ Set.Ioc (0 : ℝ) 1,
        Tendsto (fun n => hayashiRenyiEntropy s (PL n) / n) atTop (nhds R0)) →
      ∃ S : CodeSequence X B, S.size = M ∧ (∀ n, UsesLaw (PL n) (S.code n)) ∧
        Filter.limsup (fun n => (Imix (hayashiCompose (productOutput n WE) (S.code n).encoder) / n : EReal))
          atTop ≤ (max (holevo PX WE - R0) 0 : EReal)) ∧
    (∀ R : ℝ, 0 ≤ R → wiretapCapacity WB WE < (R : EReal) → R ≤ holevo PX WB →
      leakedRate WB WE R ≤ (R - (holevo PX WB - holevo PX WE) : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
