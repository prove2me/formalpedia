-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_petz_resolvability_moments
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.petz_resolvability_moments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:25:10.294176+00:00
-- url     : https://prove2.me/theorems/3d61d3a2-23bf-4208-af61-5878927d94da
-- title:
--   Unnumbered (55), (58), (61): Petz exponential-moment bounds
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Fix $0<s\le1$. In the pairwise-independent map setting, the Condition 1 submodule setting, and the Condition 2 injective-map setting respectively, the output $\rho$ and average reference $\sigma$ satisfy
--   $$\begin{aligned}
--   \mathbb E_\Phi e^{sD(\rho_\Phi\Vert\bar W_{P_X})}&\le v^s(1+e^{s(I_s(W,P_X)-H_{1+s}(P_A))}),\\
--   \mathbb E_{Z,Y}e^{sD(W\circ P_{\rm mix,C_Z+Y}\Vert\bar W_{\rm unif})}&\le v^s(1+L^{-s}e^{sI_s(W,\rm unif)}),\\
--   \mathbb E_{Z,Y}e^{sD(W\circ(f_Z+Y)\circ P_A\Vert\bar W_{\rm unif})}&\le v^s(1+e^{s(I_s(W,\rm unif)-H_{1+s}(P_A))}).
--   \end{aligned}$$
--   Every seed law is normalized; $Y$ is independent uniform; the submodule has fixed size and nonzero membership probability at most $L/|X|$, and the injective maps satisfy the nonzero bound $1/(|X|-1)$. These final bounds use Umegaki $D$ and Petz $I_s$.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 8, Unnumbered (55), (58), (61): Petz exponential-moment bounds

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

/-- PDF pp.8–9, (55),(58),(61): all three Umegaki exponential moment bounds,
with final PETZ information. The preceding underlined moments are not substituted. -/
theorem petz_resolvability_moments [Nonempty X] [Nonempty A] [Nonempty E]
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    (∀ (W : X → Matrix E E ℂ), hayashiIsCQ W → ∀ (PX : X → ℝ), IsLaw PX →
      ∀ (PA : A → ℝ), IsLaw PA → ∀ (PZ : Z → ℝ) (f : Z → A → X), PairwiseMap PZ f PX →
        expectExp PZ s (fun z => relativeEntropy (mapOutput W (f z) PA) (average W PX)) ≤
          ENNReal.ofReal (Real.rpow (eigenCount (average W PX)) s *
            (1 + Real.exp (s * (petzInfo s W PX - hayashiRenyiEntropy s PA))))) ∧
    (∀ {K G : Type} [Ring K] [AddCommGroup G] [Module K G] [Fintype G]
      (W : G → Matrix E E ℂ), hayashiIsCQ W → ∀ (PZ : Z → ℝ) (C : Z → Submodule K G)
      (L : ℕ), 0 < L → Condition1 PZ C L →
        shiftExpectExp PZ s (fun z y => relativeEntropy (cosetOutput W (C z) y) (average W uniform)) ≤
          ENNReal.ofReal (uniformMomentBound L s W uniform)) ∧
    (∀ {K D G : Type} [Ring K] [AddCommGroup D] [AddCommGroup G]
      [Module K D] [Module K G] [Fintype D] [Fintype G]
      (W : G → Matrix E E ℂ), hayashiIsCQ W → ∀ (PA : D → ℝ), IsLaw PA →
      ∀ (PZ : Z → ℝ) (f : Z → D →ₗ[K] G), Condition2 PZ f →
        shiftExpectExp PZ s (fun z y => relativeEntropy (mapOutput W (fun a => f z a + y) PA)
          (average W uniform)) ≤ ENNReal.ofReal (Real.rpow (eigenCount (average W uniform)) s *
            (1 + Real.exp (s * (petzInfo s W uniform - hayashiRenyiEntropy s PA))))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
