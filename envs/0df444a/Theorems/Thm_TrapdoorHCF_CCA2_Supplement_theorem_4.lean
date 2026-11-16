-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_theorem_4
-- name    : TrapdoorHCF.CCA2.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:42:41.953681+00:00
-- url     : https://prove2.me/theorems/93fb03ba-ca48-4822-91f4-a98d40d34811
-- title:
--   Theorem 4 — parameter-preserving lossy encryption from a fiber-hiding LTDHF
-- statement:
--   Let $l,s:\mathbb N\to\mathbb N$, let $T$ be an efficient lossy trapdoor hardcore function with designated-value length $l(\lambda)$, and let $\mathrm{FSamp}$ be a fiber sampler for $T$ with fiber-sampling randomness length $s(\lambda)$. Suppose $T$ is a perfectly correct and secure fiber-hiding LTDHF (Definition 19): it is perfectly correct, has indistinguishable modes and is statistically lossy, $\mathrm{FSamp}$ is fiber samplable in both key modes (efficiency, fiber consistency and distributional fidelity), and fiber hiding holds. Then there is a lossy public-key encryption scheme $P$ whose encryption randomness is exactly $\{0,1\}^{s(\lambda)}$ and such that
--
--   $$P\ \text{is efficient with message space }\{0,1\}^{l(\lambda)},\ \text{perfectly correct, mode indistinguishable and ciphertext lossy}.$$
--
--   The point is parameter preservation: the scheme spends only $s(\lambda)$ random bits per encryption rather than a full input of $D_\lambda$.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces D_lambda → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: base paper.md decision 5; every source input space is an instance, so the hypothesis class only grows; the constructions and experiments use only sampling
--   - reading: FSamp(pk, z; r) -> x, an input whose hEval and Eval are taken → every output of FSamp on a valid key, a label of length l(lambda) and coins lies in D_lambda, the range of the input sampler; reason: in the sampler model D_lambda is that range; Definition 17 treats FSamp outputs as inputs x of D_lambda (fiber consistency evaluates hEval on them), and Definitions 9 and 12 make correctness and efficiency statements about inputs of D_lambda only
--   - encoding: a PPT algorithm FSamp with randomness r in {0,1}^{s(lambda)} → a deterministic function of explicit coins Fin (s lambda) -> Bool, s polynomially bounded, computed by one polynomial-time machine on every valid key of either mode and every label of length l(lambda); reason: the same algorithm with its coins made explicit; Definition 17 asks for the properties in both key modes
--   - encoding: randomness space {0,1}^{s(lambda)} → P.encCoins = s; reason: encryption coins are explicit uniform vectors of that length
--   - encoding: Eval and hEval (resp. Enc) are one algorithm used with public keys generated in either mode, and hEval outputs an element of {0,1}^{l(lambda)} → one polynomial-time machine agrees with Eval (resp. hEval, Enc) on every key in the support of either key generator, and hEval has length l(lambda) under lossy keys too; reason: Definitions 7 and 12 state the algorithms once for both modes; pInv and Dec are required only for recoverable trapdoors
--   - encoding: every lossy public key in Supp(KGen_los(1^lambda)) → losKeyGen lambda r for every lossy key coin vector r; reason: the same set of keys
--   - encoding: statistical distance (1/2) sum over omega of |Pr[X = omega] - Pr[Y = omega]| → (1/2) times the real tsum over all outcomes of |p(omega) - q(omega)| for PMFs on an arbitrary type; reason: the series is absolutely summable for PMFs, so this is the same number; no finiteness of the outcome space is assumed
--   - encoding: a PPT adversary (or pair of PPT algorithms) → one uniform reactive machine with polynomial coins, state, output and total activations (RestrictedDec.Adversary with Valid), run by the base runStage with no oracle; reason: base paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 4, p.26 (proof pp.26–27); Definitions 7, 12–19

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_Lossy
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Theorem 4, p.26: a perfectly correct secure fiber-hiding LTDHF with designated-value length
`l` and fiber-sampling randomness length `s` gives a perfectly correct secure lossy PKE with
message space `{0,1}^{l(λ)}` and randomness space `{0,1}^{s(λ)}`. -/
theorem theorem_4 :
    ∀ (l s : ℕ → ℕ) (T : LTDHF) (fsamp : (lam : ℕ) → Str → Str → (Fin (s lam) → Bool) → Str),
      T.IsScheme l → T.Secure l → FiberSamplable l s T fsamp → FiberHiding l s T fsamp →
      ∃ P : LPKE, P.encCoins = s ∧ P.IsScheme l ∧ P.PerfectlyCorrect l ∧ P.Secure l := by sorry

end TrapdoorHCF.CCA2.Supplement
