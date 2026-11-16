-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_theorem_1
-- name    : TrapdoorHCF.CCA2.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:41:18.925701+00:00
-- url     : https://prove2.me/theorems/18a7123f-0fd5-452e-a33e-2f7043ec7cf6
-- title:
--   Theorem 1 — TDHFs exist iff IND-CPA public-key encryption exists
-- statement:
--   Perfectly correct secure trapdoor hardcore functions exist if and only if perfectly correct IND-CPA-secure public-key encryption schemes exist. Precisely, the following are equivalent.
--
--   1. There are a length function $l:\mathbb N\to\mathbb N$ and a trapdoor hardcore function $T$ such that $l$ is a public polynomial parameter, $l(\lambda)\ge1$ for all sufficiently large $\lambda$, $T$ is an efficient TDHF with hardcore range $\{0,1\}^{l(\lambda)}$, and $T$ is perfectly correct and secure (Definitions 9 and 10).
--   2. There are a length function $n$ and a public-key encryption scheme $P$ such that $n$ is a public polynomial parameter, $n(\lambda)\ge1$ for all sufficiently large $\lambda$, $P$ is an efficient scheme with message space $\{0,1\}^{n(\lambda)}$, and $P$ is perfectly correct and IND-CPA secure (Definitions 1 and 2).
--
--   $$\exists\,(l,T)\ \text{secure TDHF}\iff\exists\,(n,P)\ \text{perfectly correct IND-CPA PKE}.$$
--
--   This is the multi-bit analogue of the Goldwasser–Micali equivalence between trapdoor predicates and semantically secure encryption, and it is the chosen-plaintext counterpart of the mission's goal.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces D_lambda → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: base paper.md decision 5; every source input space is an instance, so the hypothesis class only grows; the constructions and experiments use only sampling
--   - reading: Definition 8/12 syntax with efficiently recognizable D_lambda and R_lambda for the constructed function → IsScheme of the constructed function asserts efficiency, the uniform sampler and output lengths but no recognizability of D_lambda or R_lambda; reason: as in the base Theorem 8: the theorem claims correctness and security; pInv is total on strings, the PKE syntax gives no recognizable randomness space, and recognizability is never used
--   - reading: perfectly correct secure TDHFs exist / perfectly correct IND-CPA PKE schemes exist → existence of a TDHF (resp. PKE) whose length l (resp. n) is a public polynomial parameter with 1 <= l(lambda) (resp. 1 <= n(lambda)) for all lambda >= some lambda0, on both sides; reason: SUPPLEMENT.md decisions S1-S2 and base decision 3: with l = 0 a TDHF whose algorithms output the empty string is perfectly correct and secure, and with n = 0 every PKE over empty messages is IND-CPA secure, so without the condition both sides are trivially true and the iff is vacuous; public length on both sides keeps both directions of the proof (Theorems 5 and 6) available
--   - encoding: a PPT adversary (or pair of PPT algorithms) → one uniform reactive machine with polynomial coins, state, output and total activations (RestrictedDec.Adversary with Valid), run by the base runStage with no oracle; reason: base paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 1, p.16 (proof in App. A, pp.32–36)

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_CPA
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Theorem 1, p.16 (proof App. A, pp.32–36): perfectly correct secure TDHFs exist iff perfectly
correct IND-CPA-secure PKE schemes exist. Lengths are public polynomial parameters, at least 1
from some security parameter on, on both sides. -/
theorem theorem_1 :
    (∃ (l : ℕ → ℕ) (T : TDHF), RestrictedDec.PolyParam l ∧ (∃ lam₀, ∀ lam ≥ lam₀, 1 ≤ l lam) ∧
      T.IsScheme l ∧ IsSecureTDHF l T) ↔
    (∃ (n : ℕ → ℕ) (P : RestrictedDec.PKE), RestrictedDec.PolyParam n ∧
      (∃ lam₀, ∀ lam ≥ lam₀, 1 ≤ n lam) ∧
      P.IsScheme n ∧ PKE.PerfectlyCorrect n P ∧ INDCPA n P) := by sorry

end TrapdoorHCF.CCA2.Supplement
