-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_repetition_is_pair
-- name    : QAlgorithms.Papers.Independent.Information100.P56.repetition_is_pair
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:25:38.142977+00:00
-- url     : https://prove2.me/theorems/98a2a059-361a-4437-9294-273f8dad6e50
-- title:
--   Section VI E, Eqs.(62)–(63): logically prefixed repetition is a pair encoder
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. In the hybrid binary channel, Bob has the binary symmetric channel of crossover $q$, while Eve receives $|\psi_b\rangle=\sqrt{q^{\prime}}|0\rangle+(-1)^b\sqrt{1-q^{\prime}}|1\rangle$. Here $q,q^{\prime}\in[0,1]$, and $x$ is the probability of input symbol $1$. Write $h$ for natural binary entropy. For $n\ge1$ and independent physical and logical flip probabilities $\lambda,\mu\in[0,1/2]$, repeat a uniform logical bit after its logical flip, then flip each physical bit independently. This is exactly the pair encoder with $P_3$ uniform on $\{0^n,1^n\}$ and
--
--   $$P_1=(1-\mu)\operatorname{Bern}(\lambda)^{\otimes n}+\mu\operatorname{Bern}(1-\lambda)^{\otimes n}.$$
--
--   Its conditional law for logical input $1$ is the translate by $1^n$, and its per-use private-information rate is
--
--   $$r_{n,\lambda,\mu}=\frac{\Delta_n(P_3*P_1)-\Delta_n(P_1)}n.$$
--
--   This rate bounds $C^{(n)}/n$ from below, and all smaller nonnegative rates are achievable. The outer uniform law is on two words.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 17, Section VI E, Eqs.(62)–(63): logically prefixed repetition is a pair encoder

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI E, p.17, Eqs.(62)–(63): logically prefixed repetition is the specified
pair encoder, with uniformity only on its two outer words, for every n>=1. -/
theorem repetition_is_pair (n : ℕ) (hn : 1 ≤ n) (q qprime lambda mu : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqp : qprime ∈ Set.Icc (0 : ℝ) 1)
    (hl : lambda ∈ Set.Icc (0 : ℝ) (1 / 2)) (hm : mu ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    IsLaw (prefixedNoise n lambda mu) ∧ IsLaw (repetitionOuter n) ∧
    (∀ (u : Bool) (z : QAlgorithms.Qubits n),
      (∑ l : Bool, bernoulli mu l *
        physicalNoise n lambda (fun i => Bool.xor (Bool.xor u l) (z i))) =
      prefixedNoise n lambda mu (fun i => Bool.xor u (z i))) ∧
    (repetitionRate n q qprime lambda mu =
      (holevo (bernoulli (1 / 2)) (fun u =>
        average (productOutput n (hybridBob q))
          (fun z => prefixedNoise n lambda mu (fun i => Bool.xor u (z i)))) -
       holevo (bernoulli (1 / 2)) (fun u =>
        average (productOutput n (hybridEve qprime))
          (fun z => prefixedNoise n lambda mu (fun i => Bool.xor u (z i))))) / n) ∧
    repetitionRate n q qprime lambda mu ≤
      blockPrivate n (hybridBob q) (hybridEve qprime) / n ∧
    (∀ R : ℝ, 0 ≤ R → R < repetitionRate n q qprime lambda mu →
      AchievableRate (hybridBob q) (hybridEve qprime) R) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
