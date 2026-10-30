-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_submodule_resolvability
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.submodule_resolvability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:23:28.717438+00:00
-- url     : https://prove2.me/theorems/85f1fbe8-8ee0-47a1-be4a-7646cd720592
-- title:
--   Lemma 5, (56)–(57): random-submodule resolvability
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Let $X$ be a finite module. A seed chooses a submodule $C_Z$ of fixed size $L\ge1$ such that $\Pr[x\in C_Z]\le L/|X|$ for every $x\ne0$. Let $Y$ be independent and uniform on $X$, put $\rho_{Z,Y}=|C_Z|^{-1}\sum_{c\in C_Z}W_{c+Y}$ and $\sigma=\bar W_{\rm unif}$. For $0<s\le1$,
--   $$\mathbb E D(\rho_{Z,Y}\Vert\sigma)\le\frac{v^s e^{sI_s(W,\rm unif)}}{L^s s},$$
--   $$\mathbb E e^{s\underline D(\rho_{Z,Y}\Vert\sigma)}\le\mathbb E T_s(\rho_{Z,Y},\sigma)\le1+\frac{|X|^{-1}\sum_xT_s(W_x,\sigma)}{L^s}.$$
--   The underlined divergence and starred moment are those defined in (2),(4), not modern sandwiched quantities.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 8, Lemma 5, (56)–(57): random-submodule resolvability

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

/-- PDF p.8, Lemma 5, (56)–(57): Condition 1 and independent ambient translation.
The first moment is Umegaki; the first exponential moment is underlined. -/
theorem submodule_resolvability {K G : Type} [Ring K] [AddCommGroup G] [Module K G]
    [Fintype G] [Nonempty E] (W : G → Matrix E E ℂ) (hW : hayashiIsCQ W)
    (PZ : Z → ℝ) (C : Z → Submodule K G) (L : ℕ) (hL : 0 < L)
    (hC : Condition1 PZ C L) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    let V := fun z y => cosetOutput W (C z) y
    let rho := average W (uniform : G → ℝ)
    shiftExpectE PZ (fun z y => relativeEntropy (V z y) rho) ≤
      ((Real.rpow (eigenCount rho) s * Real.exp (s * petzInfo s W uniform) /
        (Real.rpow L s * s) : ℝ) : EReal) ∧
    shiftExpectExp PZ s (fun z y => underlinedD (V z y) rho) ≤
      ENNReal.ofReal (shiftExpect PZ (fun z y => starMoment s (V z y) rho)) ∧
    shiftExpect PZ (fun z y => starMoment s (V z y) rho) ≤
      1 + (∑ x, (Fintype.card G : ℝ)⁻¹ * starMoment s (W x) rho) / Real.rpow L s := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
