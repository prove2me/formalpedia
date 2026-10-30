-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_ensemble_leakage
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.ensemble_leakage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:27:42.00399+00:00
-- url     : https://prove2.me/theorems/de4e5a73-b3c7-4511-9fa9-509b9f0920fe
-- title:
--   Unnumbered (65)–(67): ensemble leakage and full trace-norm bounds
-- statement:
--   All classical alphabets are finite and nonempty and all quantum systems are finite dimensional. A cq channel $W:x\mapsto W_x$ has positive semidefinite outputs of trace one; every input law is nonnegative and sums to one. Logarithms are natural. Write $I_s(W,P)$ for the paper's Petz information, $I_s^G(W,P)$ for its Gallager information, $H_{1+s}(P)$ for classical Rényi entropy, and $I_0=I_0^G=I$ for Holevo information. Matrix powers vanish on the kernel, including exponent zero. Write $\bar W_P=\sum_xP(x)W_x$, $A_s=\sum_xP(x)W_x^{1+s}$, $v$ for the number of distinct eigenvalues of $\bar W_P$, and $v_s$ for that of $A_s$. The supported spectral spread is $\lambda_s=\log\lambda_{\max}(A_s)-\log\lambda_{\min,+}(A_s)$ and $\mu_s=\min\{4+\sqrt{v_s},(4+\sqrt{\lceil\lambda_s\rceil})e^{s/2}\}$.
--
--   For a message-output cq channel $V$, $I_{\rm mix}(V)$ and $d_{1,\rm mix}(V)$ are its uniform-message Holevo information and full trace-norm correlation. Their maximum versions optimize over every message law. A code has an actual stochastic encoder and a normalized message POVM; $\epsilon$ and $\epsilon_{\max}$ denote its average and worst-message error. “Uses $P_L$” means each encoder row is a pushforward of that sole auxiliary law under a deterministic table chosen before communication.
--
--   For $M,L\ge1$, sample all table entries $c(\ell,m)$ independently from $P_X$ and encode message $m$ using $\Gamma_m(x)=\sum_\ell P_L(\ell)\mathbf1_{c(\ell,m)=x}$. For $0<s\le1$,
--   $$\mathbb E_c I_{\rm mix}(W_E\circ\Gamma)\le\frac{v^s}{s}e^{s(I_s-H_{1+s})},$$
--   $$\mathbb E_c d_{1,\rm mix}(W_E\circ\Gamma)\le(4+\sqrt{v_s})e^{\frac s2(I_s^G-H_{1+s})},$$
--   $$\mathbb E_c d_{1,\rm mix}(W_E\circ\Gamma)\le(4+\sqrt{\lceil\lambda_s\rceil})e^{\frac s2(I_s^G-H_{1+s})+s/2}.$$
--   Here $I_s,I_s^G$ refer to $(W_E,P_X)$ and $H_{1+s}$ to $P_L$. All expectations concern the table sampled before communication.
--
--   This result supplies the corresponding finite-dimensional information or coding interface for the paper's security analysis.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 10, Unnumbered (65)–(67): ensemble leakage and full trace-norm bounds

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

/-- PDF p.10, (65)–(67): expectations over the actual iid codebook, not a chosen
input. Both separate spectral branches are retained. Analysis permutations use no
additional runtime randomness. -/
theorem ensemble_leakage [Nonempty X] [Nonempty E]
    (WE : X → Matrix E E ℂ) (hE : hayashiIsCQ WE)
    (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (PX : X → ℝ) (hPX : IsLaw PX) (PL : Fin L → ℝ) (hPL : IsLaw PL)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    let V := fun c : Fin L → Fin M → X => hayashiCompose WE (tableEncoder PL c)
    (∑ c, bookLaw PX c * holevo uniform (V c)) ≤ secrecy s WE PX PL ∧
    (∑ c, bookLaw PX c * traceCorrelation uniform (V c)) ≤
      (4 + Real.sqrt (eigenCount (powerAverage s WE PX))) *
        Real.exp (s / 2 * (gallagerInfo s WE PX - hayashiRenyiEntropy s PL)) ∧
    (∑ c, bookLaw PX c * traceCorrelation uniform (V c)) ≤
      (4 + Real.sqrt (Int.ceil (spectralSpread (powerAverage s WE PX)))) *
        Real.exp (s / 2 * (gallagerInfo s WE PX - hayashiRenyiEntropy s PL) + s / 2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
