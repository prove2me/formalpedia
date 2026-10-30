-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_iid_resolvability
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.iid_resolvability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:22:33.733978+00:00
-- url     : https://prove2.me/theorems/4937209b-8c09-43bc-bb1f-89ab69f9e1cd
-- title:
--   Lemma 4, (53)–(54): non-uniform pairwise-independent random-map resolvability
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Let $P_A$ be an auxiliary law. Under a normalized finite seed law, let $\Phi(a)$ have marginal $P_X$ and be independent of $\Phi(b)$ whenever $a\ne b$. Put $\rho_\Phi=\sum_aP_A(a)W_{\Phi(a)}$ and $\sigma=\bar W_{P_X}$. For $0<s\le1$,
--   $$\mathbb E D(\rho_\Phi\Vert\sigma)\le\frac{v^s}{s}e^{-sH_{1+s}(P_A)+sI_s(W,P_X)},$$
--   $$\mathbb E e^{s\underline D(\rho_\Phi\Vert\sigma)}\le\mathbb E T_s(\rho_\Phi,\sigma)\le1+e^{-sH_{1+s}(P_A)}\sum_xP_X(x)T_s(W_x,\sigma).$$
--   Here $D$ is Umegaki entropy, $\underline D(\rho\Vert\sigma)=\operatorname{Tr}\rho\log(\sigma^{-1/2}\rho\sigma^{-1/2})$ uses an extended spectral logarithm, and $T_s(\rho,\sigma)=\operatorname{Tr}\rho(\sigma^{-1/2}\rho\sigma^{-1/2})^s=e^{sD_s^*(\rho\Vert\sigma)}$. Expectations are over the map, not the auxiliary input.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 7, Lemma 4, (53)–(54): non-uniform pairwise-independent random-map resolvability

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

/-- PDF p.7, Lemma 4, (53)–(54): map expectation, Umegaki first moment,
UNDERLINED exponential moment, and the paper's positive starred trace moment. -/
theorem iid_resolvability [Nonempty X] [Nonempty A] [Nonempty E]
    (W : X → Matrix E E ℂ) (hW : hayashiIsCQ W)
    (PX : X → ℝ) (hPX : IsLaw PX) (PA : A → ℝ) (hPA : IsLaw PA)
    (PZ : Z → ℝ) (f : Z → A → X) (hf : PairwiseMap PZ f PX)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    expectE PZ (fun z => relativeEntropy (mapOutput W (f z) PA) (average W PX)) ≤
      (secrecy s W PX PA : EReal) ∧
    expectExp PZ s (fun z => underlinedD (mapOutput W (f z) PA) (average W PX)) ≤
      ENNReal.ofReal (∑ z, PZ z * starMoment s (mapOutput W (f z) PA) (average W PX)) ∧
    (∑ z, PZ z * starMoment s (mapOutput W (f z) PA) (average W PX)) ≤
      1 + Real.exp (-s * hayashiRenyiEntropy s PA) *
        (∑ x, PX x * starMoment s (W x) (average W PX)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
