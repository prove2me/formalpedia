-- Prove2me | Theorems.Thm_TightPQRepetition_Main_corollary_5_3
-- name    : TightPQRepetition.Main.corollary_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:43:28.852627+00:00
-- url     : https://prove2.me/theorems/556c1db7-292a-4f7a-807a-b96a4e87138c
-- title:
--   Corollary 5.3 — tight threshold soundness (corrected: adversary-wise negligible functions)
-- statement:
--   Let $(P,V)$ be a protocol with polynomially many rounds and an efficient classical verifier, let $\widehat V$ be its fresh-key encrypted version under a semantically secure scheme, and let $\varepsilon=\varepsilon(\lambda)\in[0,1]$ be efficiently computable. Suppose that for every QPT adversary $A$ there is a negligible function $\mathrm{negl}$ with
--   $$\Pr[\langle A,V\rangle(1^\lambda)=1]\le\varepsilon+\mathrm{negl}(\lambda)\quad\text{for all }\lambda.$$
--   Let $k=k(\lambda)$ and $t=t(\lambda)\le k$ be polynomially bounded. Then for every QPT adversary $B$ there is a negligible function $\mathrm{negl}'$ with
--   $$\Pr[\langle B,\widehat V^{k,t}\rangle(1^\lambda)=1]\le B(k,t,\varepsilon)+\mathrm{negl}'(\lambda)\quad\text{for all }\lambda.$$
--   Here $B(k,t,\varepsilon)=\sum_{s=t}^k\binom ks\varepsilon^s(1-\varepsilon)^{k-s}$, so $t=k$ gives $\varepsilon^k+\mathrm{negl}'(\lambda)$. The adversary is one joint quantum prover with quantum advice, which may correlate all coordinates: no independence is assumed.
--
--   This is the formal Theorem 1.1, the headline of the paper: tight parallel repetition, for all threshold verifiers, of every private-coin argument after running it under homomorphic encryption.
--
--   Differences from the source:
--   - generalization: PPT verifier and encryption algorithms (uniform) → non-uniform families of polynomial-size Boolean circuits, with coins an explicit input and outputs of bounded, input-dependent length; reason: a uniform PPT algorithm gives such a family, so every source instance is covered; the source already takes all adversaries non-uniform (Remark 5.2)
--   - encoding: QPT prover with quantum advice → a family of `Strategy`: a pure advice state, one unitary circuit of one- and two-qubit gates per round, computational-basis measurement of answer wires, and a polynomial-size classical controller with a random tape; reason: purification costs polynomial overhead (PDF p. 22); the source fixes no gate set
--   - reading: there exists a negligible function negl where for every QPT adversary A, and there exists a negligible function negl′ such that for every QPT adversary B → for every QPT adversary a negligible function, in both premise and conclusion; reason: with non-uniform adversaries the printed order makes the premise statistical soundness, which no genuine argument satisfies, and then the conclusion needs no cryptography; the printed proof and Notation 1 are adversary-wise
--   - generalization: polynomials k, t → polynomially bounded functions; reason: polynomials are a special case
--   - encoding: efficiently computable ε(λ) ≥ 0 → ε(λ) ∈ [0,1], efficiently computable by a polynomial-time Turing machine to any requested precision; reason: [0,1] is the domain of B(k,t,ε) in Notation 2
--   - generalization: the scheme is a QFHE of Definition 2, or an FHE of Definition 1 for Remark 3.3 → any `EncScheme`: efficient classical Gen, Enc, Dec with semantic security, with no homomorphic evaluation or correctness required; reason: the verifier and the soundness proof use only these; `ClassicalFHE.toEncScheme` and `QFHE.toEncScheme` give the source's two cases
--   - reading: queries q_j of unspecified length → each q_j has a length depending only on λ and j; reason: the dummy Enc(0) of Algorithm 1 is prepared before the query is known, and semantic security needs |m₀| = |m₁|, so the length must be known in advance; a verifier reaches this form by padding
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Corollary 5.3, printed p. 19 / PDF p. 21; Theorem 1.1 (Informal), printed p. 2 / PDF p. 4

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Preprocess

namespace TightPQRepetition.Main

/-- Corollary 5.3 (printed p. 19, PDF p. 21), the formal Theorem 1.1. -/
theorem corollary_5_3 (E : EncScheme) (hE : E.IsEfficient) (hsec : E.IsSemanticallySecure)
    (V : Verifier) (hV : V.IsEfficient) (ε : ℕ → ℝ) (hεc : EfficientlyComputable ε)
    (hε0 : ∀ lam, 0 ≤ ε lam) (hε1 : ∀ lam, ε lam ≤ 1) (hsound : V.IsSound ε)
    (k t : ℕ → ℕ) (hk : PolyBound k) (ht : PolyBound t) (htk : ∀ lam, t lam ≤ k lam) :
    ∀ B : ℕ → Strategy, IsQPT B → ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ lam,
      (B lam).acceptProb (hatPar E V (k lam) (t lam)) lam ≤
        binomTail (k lam) (t lam) (ε lam) + μ lam := by sorry

end TightPQRepetition.Main
