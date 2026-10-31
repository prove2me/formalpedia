-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_deterministic_security
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.deterministic_security
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:01:07.21056+00:00
-- url     : https://prove2.me/theorems/948198d6-ea65-4d19-88f4-3db27b6cee9e
-- title:
--   §VII.B, equations (62)–(63): deterministic privacy amplification uniform in Pauli parameters
-- statement:
--   Use $n\ge1$ independent uses of the qubit Pauli channel $Z^xX^z$, with independent single-qubit phase and bit probabilities $p_{\rm ph},p_{\rm bit}\in[0,1]$. Eve holds the entire complementary environment. A uniform message is a coset of $L/K$, with $K\le L\le\mathbb F_2^n$; Alice sends the uniform mixture of words in that coset. Bob uses maximum-likelihood word decoding in $L$ followed by projection modulo $K$. Let $D(K,L)$ be the full trace norm between the actual cq state and the independent uniform-key state, and let $\chi(K,L)$ be its Holevo information in bits. Let $P_{\rm ph}(K,L)$ be the actual ML quotient decoding error for $K^\perp/L^\perp$ under the phase marginal of this same Pauli law. The environment, decoder, and both leakage quantities are computed explicitly, rather than supplied as unrelated data. Set $\eta_l(u)=h(u)+lu$ for $0\le u\le1/2$, and $\eta_l(u)=1+lu$ for $u>1/2$, where $h$ is binary entropy in bits. For $s\in[0,1]$ and $p\in[0,1]$, define $E_0(s,p)=s-(1+s)\log_2(p^{1/(1+s)}+(1-p)^{1/(1+s)})$ and $E(R,p)=\max_{0\le s\le1}[-sR+E_0(s,p)]$. Given $L$ and $0\le t\le\dim L$, there exists a fixed dimension-$t$ subcode $K\le L$, selected before either Pauli parameter, such that, with $S=t/n$ and $l=\dim L-t$,
--
--   $$\forall p_{\rm ph},p_{\rm bit}\in[0,1],\quad D(K,L)\le\sqrt{n+1}\,2^{-nE(1-S,p_{\rm ph})/2+3/2},\qquad\chi(K,L)\le\eta_l((n+1)2^{-nE(1-S,p_{\rm ph})}).$$
--
--   The encoder is deterministic and the channel's full environment is included. At $t=0$ these are the source's trivial privacy bounds, rather than a positive-rate security assertion.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 14, §VII.B, equations (62)–(63): deterministic privacy amplification uniform in Pauli parameters

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF pp.14--15, (62),(63): one deterministic subcode is chosen before either
Pauli parameter; its transcript contains no unknown private seed.
The endpoint t=0 is permitted and yields only the source's trivial bound. -/
theorem deterministic_security {n t : ℕ} (hn : 0 < n) (large : BinaryLinearCode n)
    (ht : t ≤ Module.finrank (ZMod 2) large) :
    ∃ small : BinaryLinearCode n, small ≤ large ∧ Module.finrank (ZMod 2) small = t ∧
      ∀ pPhase pBit : ℝ, pPhase ∈ Set.Icc 0 1 → pBit ∈ Set.Icc 0 1 →
        traceLeak small large (iidPauli pPhase pBit) ≤
          Real.sqrt (n + 1) * (2 : ℝ) ^
            (-(1 / 2 : ℝ) * n * gallagerExponent (1 - (t : ℝ) / n) pPhase + 3 / 2) ∧
        holevoLeak small large (iidPauli pPhase pBit) ≤
          entropyEnvelope (messageLength small large)
            ((n + 1) * (2 : ℝ) ^ (-(n : ℝ) * gallagerExponent (1 - (t : ℝ) / n) pPhase)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
