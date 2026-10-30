-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_independent_error_specialization
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.independent_error_specialization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:42:22.714377+00:00
-- url     : https://prove2.me/theorems/56787546-0a2c-4fd8-bed8-cc0d92b3073c
-- title:
--   Unnumbered (161)–(167): independent-error cq specialization
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   Let $P,P_Z$ be normalized laws on $\mathbb Z_d$, $d\ge1$, and let $|\psi_j\rangle=\sum_x\omega^{jx}\sqrt{P(x)}|x\rangle$, $V_j=|\psi_j\rangle\langle\psi_j|$. For independent error coordinates, the full cq family factors as
--   $$W_j=V_j\otimes\operatorname{diag}(P_Z),\qquad |\mathbb Z_d|^{-1}\sum_jV_j=\operatorname{diag}(P).$$
--   For $0\le s\le1$, discarding the $j$-independent register preserves $I,I_s,I_s^G$, and
--   $$I_s(V,\rm unif)=H_{1-s}(P),\qquad I(V,\rm unif)=H(P).$$
--   For any $R\ge0$,
--   $$e_R=\max_{0\le t\le1}t(R-H_{1-t}(P)),\qquad e_G=\max_{0\le t\le1}\frac t2(R-H_{1/(1+t)}(P)).$$
--   Both exponents are positive for $R>H(P)$. Rényi entropy uses the Shannon limit at one and positive support at order zero; no equality of matrices on different spaces is asserted.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 26, Unnumbered (161)–(167): independent-error cq specialization

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

/-- PDF p.26, (161)–(167): independent-error factorization and exact information
equalities after discarding the j-independent register, rather than an equality of
matrices of different sizes. No bit/phase interpretation of (151) is asserted. -/
theorem independent_error_specialization (d : ℕ) [NeZero d]
    (P PZ : ZMod d → ℝ) (hP : IsLaw P) (hPZ : IsLaw PZ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (R : ℝ) (hR : 0 ≤ R) :
    (∀ j u v, phaseCQ d PZ (fun _ => P) j u v =
      phasePure d P j u.1 v.1 * (if u.2 = v.2 then (PZ u.2 : ℂ) else 0)) ∧
    average (phasePure d P) uniform = Matrix.diagonal (fun x => (P x : ℂ)) ∧
    petzInfo s (phaseCQ d PZ (fun _ => P)) uniform = petzInfo s (phasePure d P) uniform ∧
    holevo uniform (phaseCQ d PZ (fun _ => P)) = holevo uniform (phasePure d P) ∧
    gallagerInfo s (phaseCQ d PZ (fun _ => P)) uniform = gallagerInfo s (phasePure d P) uniform ∧
    petzInfo s (phasePure d P) uniform = classicalRenyi (1 - s) P ∧
    holevo uniform (phasePure d P) = hayashiShannon P ∧
    exponentR R (phasePure d P) uniform =
      sSup {y : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) 1, y = t * (R - classicalRenyi (1 - t) P)} ∧
    exponentG R (phasePure d P) uniform =
      sSup {y : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) 1, y = t / 2 * (R - classicalRenyi (1 / (1 + t)) P)} ∧
    (hayashiShannon P < R → 0 < exponentR R (phasePure d P) uniform ∧
      0 < exponentG R (phasePure d P) uniform) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
