-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_5
-- name    : RestrictedDec.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:38:45.31204+00:00
-- url     : https://prove2.me/theorems/91e7c1fe-ddeb-4ab4-8695-e081a9a89faa
-- title:
--   Theorem 5 — the unsigned CHK compiler is in $\mathrm{Sec}^{na}(q)$ but not in $\mathrm{Sec}^{ad}(q)$
-- statement:
--   Let $M$ be a common message space and $q$ a public observation with its public algorithms $\mathrm{Valid}_q$ and $\mathrm{Rep}_q$ (§2.3). Let
--
--   1. $R$ be an efficient, IND-CPA-secure residual scheme over $M$ with ordinary correctness (Definitions 2, 3);
--   2. $I$ be an efficient IBE that is selective-identity IND-CPA secure and ordinarily correct (Definitions 6, 7), whose public identity space contains $\{0,1\}^\lambda$ and is efficiently recognizable, and whose message space contains every valid label;
--   3. $P$ be an efficient secure PRF on the identity space whose outputs have the length of the extraction tape (stable per-identity extraction, Lemma 2).
--
--   Then the unsigned scheme (4.4) satisfies $\mathrm{IND}^{na}_{\mathcal F_q}$ security, including ordinary correctness:
--   $$\mathrm{Unsigned}_q\in\mathrm{Sec}^{na}(q).$$
--   If moreover a uniform PPT sampler, run independently of the generated keys, always outputs valid equal-length messages $u_0,u_1$ with $q(u_0)\neq q(u_1)$, then the unsigned scheme does not satisfy $\mathrm{IND}^{ad}_{\mathcal F_q}$:
--   $$\mathrm{Unsigned}_q\notin\mathrm{Sec}^{ad}(q).$$
--
--   Without a signature, an adaptive adversary can replace the residual component of the challenge and keep its label ciphertext, so the label of the challenge is revealed; before the challenge, the fresh random identity is unpredictable.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: Sec^t(q) = Sec^t(F_q), F_q = {g ∘ q : g an admissible circuit / efficient public postprocessing} → SecM t M (famObs q); reason: the published famObs is the class of §2.3, p.14
--   - encoding: PPT primitives (R, L, I, P, S, N, q, samplers) → separate efficiency hypotheses (IsSchemeM, IsEfficient, IsPublic, IsObsMap); reason: the paper's PPT convention; the reductions run these algorithms
--   - reading: IBE extraction is stable per identity, using a secure PRF → the compiler derives the extraction tape PRF_k(id) with k in the secret key; P is a secure PRF on the identity space with outputs of length r_ext(λ); reason: §4.2, p.24 and Lemma 2, p.31
--   - reading: identities include the identities the compiler uses; the IBE message space contains every valid q-label → hypotheses on the identity space Id and the message space Ym of I; reason: §4.2, p.24 ('Its identities include a canonical, injective encoding of one-time verification keys; its message space contains every valid q-label')
--   - reading: a public identity space I_λ; malformed encodings are rejected → Id is efficiently recognizable and a ciphertext whose identity is outside Id_λ is malformed (⊥); reason: App. A.3, p.31 ('a public identity space Iλ'); decryption 'Reject malformed encodings', p.25; without the test the IBE and PRF reductions could not answer queries on identities outside I_λ
--   - encoding: ciphertext tuples and malformed encodings → canonical tuple codes; malformed = not the code of a tuple of the right length; reason: an unambiguous canonical encoding, p.24
--   - encoding: two efficiently found valid equal-length messages u₀, u₁, sampled independently of the generated keys, with q(u₀) ≠ q(u₁) → a uniform PPT sampler (no key input) every output of which is a valid equal-length pair with q(u₀) ≠ q(u₁); reason: 'sampled independently of the generated keys', p.25
--   - encoding: the common message space → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 5, p.25; (4.4), p.25

import Mathlib
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_INDCPAM
import Definitions.Def_RestrictedDec_Supplement_Sampler
import Definitions.Def_RestrictedDec_Supplement_unsignedCHK
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 5** (the unsigned CHK compiler is pre-challenge `q`-secure, not adaptively
`q`-secure). Let `M` be a common message space and `q` a public observation with its algorithms
`Valid_q`, `Rep_q` (§2.3). Let `R` be an efficient, IND-CPA-secure, ordinarily correct residual
scheme over `M`; `I` an efficient, selective-identity IND-CPA-secure, ordinarily correct IBE whose
identity space contains `{0,1}^λ` and whose message space contains every valid label; and `P` an
efficient secure PRF on the identity space with outputs of the extraction-coin length (stable
per-identity extraction). Then
1. the unsigned scheme (4.4) is in `Sec^na(q)` (including ordinary correctness);
2. if a uniform PPT sampler, run independently of the keys, always outputs valid equal-length
   messages `u₀, u₁` with `q(u₀) ≠ q(u₁)`, the unsigned scheme is not in `Sec^ad(q)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 5, p.25; construction
(4.4), p.25; Definitions 2, 3, 5, 6, 7, pp.29–31.

**Formalization Note.** `Sec^t(q)` is `Sec^t(famObs q)`. The identity space `Id` is also the PRF
domain. -/
theorem theorem_5 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M) (o : Obs) (ho : o.IsPublic M)
    (R : PKE) (hR : IsSchemeM M R) (hRcpa : INDCPAM M R) (hRcor : CorrectM M R)
    (I : IBE) (Id Ym : ℕ → Str → Prop) (hI : I.IsEfficient)
    (hIdrec : Recognizable Id) (hId : ∀ (lam : ℕ) (i : Str), i.length = lam → Id lam i)
    (hYm : ∀ (lam : ℕ) (y : Str), o.valid lam y = true → Ym lam y)
    (hIsec : I.SelINDCPA Id Ym) (hIcor : I.Correct Id Ym)
    (P : PRF) (hPlen : ∀ lam, P.outLen lam = I.extCoins lam) (hP : P.IsEfficient Id)
    (hPsec : P.Secure Id) :
    SecM .na M (famObs o.q) (unsignedCHK M Id o R I P) ∧
    ((∃ W : Sampler, W.IsEfficient ∧ ∀ lam (ρ : Fin (W.coins lam) → Bool),
        M lam (W.out lam ρ).1 ∧ M lam (W.out lam ρ).2 ∧
        (W.out lam ρ).1.length = (W.out lam ρ).2.length ∧
        o.q lam (some (W.out lam ρ).1) ≠ o.q lam (some (W.out lam ρ).2)) →
      ¬ SecM .ad M (famObs o.q) (unsignedCHK M Id o R I P)) := by sorry

end Supplement

end RestrictedDec
