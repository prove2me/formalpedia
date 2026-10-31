-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_iid_security
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.iid_security
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:41:27.681362+00:00
-- url     : https://prove2.me/theorems/af547405-9bd4-45a5-8e8f-0a0b86db10a4
-- title:
--   §VII.A, equations (59)–(61): dual-universal privacy amplification on an iid Pauli wire-tap channel
-- statement:
--   Let $n\ge1$ and let $C_r\le\mathbb F_2^n$ be indexed by a finite nonempty seed set $I$, sampled uniformly and independently of inputs. Repeated codes at distinct seeds retain their multiplicity. Write $t_{\min}=\min_r\dim C_r$ and $t_{\max}=\max_r\dim C_r$. A dimension-$t$ universality bound means $\Pr_r[x\in C_r]\le\varepsilon 2^{t-n}$ for every nonzero $x$. Use $n\ge1$ independent uses of the qubit Pauli channel $Z^xX^z$, with independent single-qubit phase and bit probabilities $p_{\rm ph},p_{\rm bit}\in[0,1]$. Eve holds the entire complementary environment. A uniform message is a coset of $L/K$, with $K\le L\le\mathbb F_2^n$; Alice sends the uniform mixture of words in that coset. Bob uses maximum-likelihood word decoding in $L$ followed by projection modulo $K$. Let $D(K,L)$ be the full trace norm between the actual cq state and the independent uniform-key state, and let $\chi(K,L)$ be its Holevo information in bits. Let $P_{\rm ph}(K,L)$ be the actual ML quotient decoding error for $K^\perp/L^\perp$ under the phase marginal of this same Pauli law. The environment, decoder, and both leakage quantities are computed explicitly, rather than supplied as unrelated data. Set $\eta_l(u)=h(u)+lu$ for $0\le u\le1/2$, and $\eta_l(u)=1+lu$ for $u>1/2$, where $h$ is binary entropy in bits. For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. Fix $L$ and a subcode family $K_r\le L$ whose dual extended-code family is $\varepsilon$-almost universal at its maximum dimension, with $\varepsilon>0$. Set $t=\min_r\dim K_r$, $S=t/n$, $l_r=\dim L-\dim K_r$, $l_{\max}=\dim L-t$, and $B=2^{-nE(1-S,p_{\rm ph})}\max\{\varepsilon,1\}$. Then
--
--   $$D(K_r,L)\le2\sqrt{2P_{\rm ph}(K_r,L)},\quad\chi(K_r,L)\le\eta_{l_r}(P_{\rm ph}(K_r,L)),$$
--   $$\mathbb E_rP_{\rm ph}(K_r,L)\le B,\qquad\mathbb E_rD(K_r,L)\le2^{-nE(1-S,p_{\rm ph})/2+3/2}\max\{\sqrt\varepsilon,1\},\qquad\mathbb E_r\chi(K_r,L)\le\eta_{l_{\max}}(B).$$
--
--   The public seed is retained in Eve's cq blocks. These finite physical inequalities do not identify coherent and incoherent complementary outputs.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 14, §VII.A, equations (59)–(61): dual-universal privacy amplification on an iid Pauli wire-tap channel

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.13--14, (54),(55),(59)--(61): finite physical iid wire-tap security.
S=min dim(C2)/n; the swapped dimensions below (59) are corrected using (56).
Each seed has its own quotient and message length, bounded by l_max.
The seed is public: the uniform average is the cq block sum with Eve's seed record. -/
theorem iid_security {n : ℕ} (hn : 0 < n) {I : Type*} [Fintype I] [Nonempty I]
    (large : BinaryLinearCode n) (small : I → BinaryLinearCode n) (hsub : ∀ r, small r ≤ large)
    (eps : ℝ) (heps : 0 < eps)
    (hu : ExtUniversalAt (binDual large) (fun r => binDual (small r))
      (maxDim (fun r => binDual (small r))) eps)
    (pPhase pBit : ℝ) (hp : pPhase ∈ Set.Icc 0 1) (hb : pBit ∈ Set.Icc 0 1) :
    (∀ r, traceLeak (small r) large (iidPauli pPhase pBit) ≤
      2 * Real.sqrt (2 * phaseError (small r) large (iidPauli pPhase pBit))) ∧
    (∀ r, holevoLeak (small r) large (iidPauli pPhase pBit) ≤
      entropyEnvelope (messageLength (small r) large) (phaseError (small r) large (iidPauli pPhase pBit))) ∧
    avg (fun r => phaseError (small r) large (iidPauli pPhase pBit)) ≤
      iidPhaseBound n (minDim small) pPhase eps ∧
    avg (fun r => traceLeak (small r) large (iidPauli pPhase pBit)) ≤
      (2 : ℝ) ^ (-(1 / 2 : ℝ) * n * gallagerExponent (1 - (minDim small : ℝ) / n) pPhase + 3 / 2) *
        max (Real.sqrt eps) 1 ∧
    avg (fun r => holevoLeak (small r) large (iidPauli pPhase pBit)) ≤
      entropyEnvelope (Module.finrank (ZMod 2) large - minDim small)
        (iidPhaseBound n (minDim small) pPhase eps) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
