-- Prove2me | Theorems.Thm_QiOPoQ_gol90_owf_from_far_indistinguishable
-- name    : QiOPoQ.gol90_owf_from_far_indistinguishable
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:23.685414+00:00
-- url     : https://prove2.me/theorems/11104cc9-33ae-4b22-913c-20ed19b2a128
-- title:
--   [Gol90, Theorem 2.8] as used: indistinguishable, statistically far samplers give a one-way function
-- statement:
--   Let $S_0,S_1$ be uniform classical PPT samplers on $1^\lambda$ with output laws $D_{0,\lambda},D_{1,\lambda}$. Suppose every non-uniform classical PPT distinguisher has negligible advantage in telling $D_{0,\lambda}$ from $D_{1,\lambda}$, and that for a negligible $\mu$,
--
--   $$
--   \mathrm{TV}(D_{0,\lambda},D_{1,\lambda})\ge1-\mu(\lambda).
--   $$
--
--   Then there is a one-way function secure against non-uniform classical PPT algorithms.
--
--   The paper applies this to the laws of $\mathrm{qiO}(1^\lambda,C_{0,\lambda})$ and $\mathrm{qiO}(1^\lambda,C_{1,\lambda})$.
--
--   Differences from the source:
--   - encoding: PPT and non-uniform algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count, a polynomially bounded advice string, and fixed self-delimiting encodings; reason: the standard model; a machine using at most p coins reads exactly p
--   - reading: [Gol90, Theorem 2.8] is cited for pseudorandom generators, "and therefore classically secure one-way functions"; the theorem itself is not printed in this source → the citing sentence, in the form the proof applies: efficiently samplable, indistinguishable and (1 − negl)-far ensembles give a one-way function secure against non-uniform PPT; reason: Lemma 4.5 and Theorem 4.7 use only the one-way function; the generator is an intermediate step of the citation
--   - encoding: a one-way function family {f_λ}, f_λ with input length λ, f := f_t → one polynomial-time map f on all strings (f_λ = f on length λ), inverted successfully by any preimage of any length; Figure 6 applies f to the t(λ)-bit string b; reason: the standard notion of a one-way function; same instances
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.5, p.20, citing O. Goldreich, A note on computational indistinguishability, Information Processing Letters 34(6):277–281, 1990, Theorem 2.8

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_NUPPT
import Definitions.Def_QiOPoQ_IsOWF
import Definitions.Def_QiOPoQ_samplerTV
set_option autoImplicit false
open QAdvFew.PoQOracle QAlgorithms.Complexity

namespace QiOPoQ

/-- **[Gol90, Theorem 2.8], in the form used in the proof of Lemma 4.5.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), proof of
Lemma 4.5, p.20: "By Lemma 4.4, Ĉ_{0,λ} and Ĉ_{1,λ} are computationally indistinguishable to
classical PPT adversaries. On the other hand, by correctness of the obfuscator qiO, these
distributions are statistically far, with total variation distance at least 1 − negl(λ). By
Theorem 2.8 of [Gol90], this implies that there exist classically secure pseudorandom
generators, and therefore classically secure one-way functions."

Let `S_0, S_1` be uniform classical PPT samplers on `1^λ`, with output laws `D_{0,λ}`,
`D_{1,λ}`. If every non-uniform classical PPT distinguisher has negligible advantage, and
`TV(D_{0,λ}, D_{1,λ}) ≥ 1 − μ(λ)` for a negligible `μ`, then a one-way function secure against
non-uniform classical PPT algorithms exists.

**Formalization Note.** The cited theorem (O. Goldreich, *A note on computational
indistinguishability*, IPL 34, 1990) is stated in exactly the form in which the proof applies it:
two efficiently samplable ensembles, computationally indistinguishable and statistically
`(1 − negl)`-far. The intermediate pseudorandom generator is not part of the statement. -/
theorem gol90_owf_from_far_indistinguishable (S0 S1 : UPPT)
    (hind : ∀ A : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n,
      |S0.expect (unary n) (A.acc n) - S1.expect (unary n) (A.acc n)| ≤ μ n)
    (hfar : ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, 1 - μ n ≤ samplerTV S0 S1 n) :
    ∃ f : Str → Str, IsOWF f := by sorry

end QiOPoQ
