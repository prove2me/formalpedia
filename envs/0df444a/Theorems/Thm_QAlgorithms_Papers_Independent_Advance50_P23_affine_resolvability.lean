-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_affine_resolvability
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.affine_resolvability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:24:30.66332+00:00
-- url     : https://prove2.me/theorems/2fe0ae19-ce3e-4c50-9e0e-04990d0a6c0b
-- title:
--   Lemma 6, (59)–(60): random injective affine encoding
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Let $A,X$ be finite modules and $f_Z:A\to X$ injective linear maps. For fixed nonzero $a,x$, assume $\Pr[f_Z(a)=x]\le1/(|X|-1)$ when $|X|>1$. Let $Y$ be independent uniform on $X$, $P_A$ any law, $\rho_{Z,Y}=\sum_aP_A(a)W_{f_Z(a)+Y}$ and $\sigma=\bar W_{\rm unif}$. For $0<s\le1$,
--   $$\mathbb E D(\rho_{Z,Y}\Vert\sigma)\le\frac{v^s}{s}e^{-sH_{1+s}(P_A)+sI_s(W,\rm unif)},$$
--   $$\mathbb E e^{s\underline D(\rho_{Z,Y}\Vert\sigma)}\le\mathbb E T_s(\rho_{Z,Y},\sigma)\le1+e^{-sH_{1+s}(P_A)}|X|^{-1}\sum_xT_s(W_x,\sigma).$$
--   The underlined divergence and starred trace moment are (2),(4). The singleton ambient module is included: the nonzero condition is then vacuous.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 8, Lemma 6, (59)–(60): random injective affine encoding

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

/-- PDF p.8, Lemma 6, (59)–(60): injective linear maps obeying Condition 2,
nonuniform PA, and an independent uniform translation. The singleton case is included. -/
theorem affine_resolvability {K D G : Type} [Ring K] [AddCommGroup D] [AddCommGroup G]
    [Module K D] [Module K G] [Fintype D] [Fintype G] [Nonempty E]
    (W : G → Matrix E E ℂ) (hW : hayashiIsCQ W) (PA : D → ℝ) (hPA : IsLaw PA)
    (PZ : Z → ℝ) (f : Z → D →ₗ[K] G) (hf : Condition2 PZ f)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    let V := fun z y => mapOutput W (fun a => f z a + y) PA
    let rho := average W (uniform : G → ℝ)
    shiftExpectE PZ (fun z y => relativeEntropy (V z y) rho) ≤
      (secrecy s W uniform PA : EReal) ∧
    shiftExpectExp PZ s (fun z y => underlinedD (V z y) rho) ≤
      ENNReal.ofReal (shiftExpect PZ (fun z y => starMoment s (V z y) rho)) ∧
    shiftExpect PZ (fun z y => starMoment s (V z y) rho) ≤
      1 + Real.exp (-s * hayashiRenyiEntropy s PA) *
        (∑ x, (Fintype.card G : ℝ)⁻¹ * starMoment s (W x) rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
