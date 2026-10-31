-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_comparison
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:01:53.111013+00:00
-- url     : https://prove2.me/theorems/5df1f3f6-8cf7-49a0-86c6-1c26d647b80c
-- title:
--   §VII.C, equations (67)–(70): quantitative comparison of the two approaches
-- statement:
--   Use $n\ge1$ independent uses of the qubit Pauli channel $Z^xX^z$, with independent single-qubit phase and bit probabilities $p_{\rm ph},p_{\rm bit}\in[0,1]$. Eve holds the entire complementary environment. A uniform message is a coset of $L/K$, with $K\le L\le\mathbb F_2^n$; Alice sends the uniform mixture of words in that coset. Bob uses maximum-likelihood word decoding in $L$ followed by projection modulo $K$. Let $D(K,L)$ be the full trace norm between the actual cq state and the independent uniform-key state, and let $\chi(K,L)$ be its Holevo information in bits. Let $P_{\rm ph}(K,L)$ be the actual ML quotient decoding error for $K^\perp/L^\perp$ under the phase marginal of this same Pauli law. The environment, decoder, and both leakage quantities are computed explicitly, rather than supplied as unrelated data. Set $\eta_l(u)=h(u)+lu$ for $0\le u\le1/2$, and $\eta_l(u)=1+lu$ for $u>1/2$, where $h$ is binary entropy in bits. For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. Consider block lengths $n=k+1$, finite nonempty uniform seed sets $I_k$, fixed outer codes $L_k$, and subcodes $K_{k,r}\le L_k$ whose dual extended-code families are $\varepsilon_k$-almost universal at their maximum dimensions. Assume $\varepsilon_k>0$, $\varepsilon_k\le C(k+1)^d$ for all $k\ge K_0$, for fixed $C>0,d,K_0$, and $S_k=\min_r\dim K_{k,r}/(k+1)\to S\in[0,1]$. For fixed Pauli parameters, let $\overline D_k$ and $\overline\chi_k$ be the seed averages of the actual leakage. With $-\log_2 0=+\infty$,
--
--   $$\liminf_{k\to\infty}\frac{-\log_2\overline D_k}{k+1}\ge\tfrac12E(1-S,p_{\rm ph}),\qquad\liminf_{k\to\infty}\frac{-\log_2\overline\chi_k}{k+1}\ge\tfrac12E(1-S,p_{\rm ph}),\qquad\liminf_{k\to\infty}\frac{-\log_2\overline\chi_k}{k+1}\ge E(1-S,p_{\rm ph}).$$
--
--   For the explicit bounds $T_n=2^{-nE(1-S,p_{\rm ph})/2+3/2}\max\{\sqrt\varepsilon,1\}$ and $U_n=(4+\sqrt{n+1}\sqrt\varepsilon)2^{-nE(1-S,p_{\rm ph})/2}$, if every $\varepsilon_k\ge1$, then
--
--   $$\frac{T_{k+1}}{U_{k+1}}=\frac{2^{3/2}\sqrt{\varepsilon_k}}{4+\sqrt{k+2}\sqrt{\varepsilon_k}}\longrightarrow0.$$
--
--   These compare upper bounds; no strict comparison of actual leakage is asserted. Natural-log rate conventions multiply each base-two exponent by $\ln2$.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 14, §VII.C, equations (67)–(70): quantitative comparison of the two approaches

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.14 (67)--(70): actual leakage exponents for polynomial epsilon growth,
with integer code rates converging to S. Equation (69) is the estimate obtained
from (65); (70) gives the full gallagerExponent exponent. All logs here are base two;
the corresponding natural-log rates are multiplied by ln(2).
The ratio compares explicit bounds, not actual leakage from two protocols. -/
theorem comparison {I : ℕ → Type*} [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    (large : (k : ℕ) → BinaryLinearCode (k + 1))
    (small : (k : ℕ) → I k → BinaryLinearCode (k + 1))
    (hsub : ∀ k r, small k r ≤ large k) (eps : ℕ → ℝ)
    (heps : ∀ k, 0 < eps k)
    (hu : ∀ k, ExtUniversalAt (binDual (large k)) (fun r => binDual (small k r))
      (maxDim (fun r => binDual (small k r))) (eps k))
    (hpoly : ∃ (C : ℝ) (d K : ℕ), 0 < C ∧
      ∀ k ≥ K, eps k ≤ C * ((k + 1 : ℕ) : ℝ) ^ d)
    (S : ℝ) (hS : S ∈ Set.Icc 0 1)
    (hrate : Filter.Tendsto (fun k => (minDim (small k) : ℝ) / (k + 1))
      Filter.atTop (nhds S))
    (pPhase pBit : ℝ) (hp : pPhase ∈ Set.Icc 0 1) (hb : pBit ∈ Set.Icc 0 1) :
    (Filter.liminf (fun k => logRate (k + 1)
      (avg (fun r => traceLeak (small k r) (large k) (iidPauli pPhase pBit)))) Filter.atTop ≥
        ((gallagerExponent (1 - S) pPhase / 2 : ℝ) : EReal)) ∧
    (Filter.liminf (fun k => logRate (k + 1)
      (avg (fun r => holevoLeak (small k r) (large k) (iidPauli pPhase pBit)))) Filter.atTop ≥
        ((gallagerExponent (1 - S) pPhase / 2 : ℝ) : EReal)) ∧
    (Filter.liminf (fun k => logRate (k + 1)
      (avg (fun r => holevoLeak (small k r) (large k) (iidPauli pPhase pBit)))) Filter.atTop ≥
        (gallagerExponent (1 - S) pPhase : EReal)) ∧
    ((∀ k, 1 ≤ eps k) →
      (∀ k, phaseTraceBound (k + 1) S pPhase (eps k) /
          deltaTraceBound (k + 1) S pPhase (eps k) =
        (2 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (eps k) /
          (4 + Real.sqrt (k + 2) * Real.sqrt (eps k))) ∧
      Filter.Tendsto (fun k => phaseTraceBound (k + 1) S pPhase (eps k) /
        deltaTraceBound (k + 1) S pPhase (eps k)) Filter.atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
