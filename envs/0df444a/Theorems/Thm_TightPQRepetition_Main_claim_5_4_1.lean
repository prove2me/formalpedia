-- Prove2me | Theorems.Thm_TightPQRepetition_Main_claim_5_4_1
-- name    : TightPQRepetition.Main.claim_5_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:40:12.019921+00:00
-- url     : https://prove2.me/theorems/df1d68db-bdff-46ef-997c-7fb471657b15
-- title:
--   Claim 5.4.1 — encrypted key-chain indistinguishability
-- statement:
--   For an efficient semantically secure scheme and every family of first queries $q_1$ of the right length, let $D_{0,\lambda}$ and $D_{1,\lambda}$ output fresh public keys for all $m$ rounds, the encrypted key chain $\widehat{\rm sk}_{\ell-1}={\rm Enc}({\rm pk}_\ell,{\rm sk}_{\ell-1})$, encryptions of zero in rounds $\ell\ge2$, and in the first round an encryption of $0$ for $D_0$ and of $q_1$ for $D_1$. Then $D_{0,\lambda}$ and $D_{1,\lambda}$ are computationally indistinguishable to polynomial-size quantum adversaries with quantum advice.
--
--   The fresh key per round is what allows the secret keys in the chain to be removed one at a time.
--
--   Differences from the source:
--   - generalization: PPT verifier and encryption algorithms (uniform) → non-uniform families of polynomial-size Boolean circuits, with coins an explicit input and outputs of bounded, input-dependent length; reason: a uniform PPT algorithm gives such a family, so every source instance is covered; the source already takes all adversaries non-uniform (Remark 5.2)
--   - encoding: the plaintext 0 of ct_ℓ → the zero string of the length of the real query of round ℓ; reason: Definition 2 needs |m₀| = |m₁|
--   - encoding: samples (pk₁, ct₁, pk₂, sk̂₁, ct₂, …) → the same values, grouped per round in the format of the messages of V̂; reason: an injective rearrangement
--   - reading: q₁ is fixed by the coupling in the proof of Lemma 5.4 → the claim holds for every family q₁ of the query length; reason: the proof treats q₁ as a fixed message
--   - generalization: the scheme is a QFHE of Definition 2, or an FHE of Definition 1 for Remark 3.3 → any `EncScheme`: efficient classical Gen, Enc, Dec with semantic security, with no homomorphic evaluation or correctness required; reason: the verifier and the soundness proof use only these; `ClassicalFHE.toEncScheme` and `QFHE.toEncScheme` give the source's two cases
--   - reading: queries q_j of unspecified length → each q_j has a length depending only on λ and j; reason: the dummy Enc(0) of Algorithm 1 is prepared before the query is known, and semantic security needs |m₀| = |m₁|, so the length must be known in advance; a verifier reaches this form by padding
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Claim 5.4.1 and the definition of D_{0,λ}, D_{1,λ}, printed p. 24 / PDF p. 26

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Encryption

namespace TightPQRepetition.Main

/-- Claim 5.4.1 (printed p. 24, PDF p. 26). -/
theorem claim_5_4_1 (E : EncScheme) (hE : E.IsEfficient) (hsec : E.IsSemanticallySecure)
    (V : Verifier) (hV : V.IsEfficient) (q₁ : ℕ → Bits)
    (hq : ∀ lam, (q₁ lam).length = V.qLen lam 0) :
    CompIndist (chainCoins E V) (chainCoins E V)
      (fun lam => chainSample E V lam (zeros (V.qLen lam 0)))
      (fun lam => chainSample E V lam (q₁ lam)) := by sorry

end TightPQRepetition.Main
