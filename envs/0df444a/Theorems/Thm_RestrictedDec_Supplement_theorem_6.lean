-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_6
-- name    : RestrictedDec.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:39:36.694473+00:00
-- url     : https://prove2.me/theorems/4ce05ed7-a7f2-4c42-af9a-697e10277c64
-- title:
--   Theorem 6 — the signed CHK compiler is in $\mathrm{Sec}^{ad}(q)$
-- statement:
--   Let $M$ be a common message space and $q$ a public observation with $\mathrm{Valid}_q$ and $\mathrm{Rep}_q$. Assume
--
--   1. $R$ is an efficient, IND-CPA-secure, ordinarily correct residual scheme over $M$;
--   2. $S$ is an efficient, correct, strongly unforgeable one-time signature (Definitions 13, 14);
--   3. $I$ is an efficient, selective-identity IND-CPA-secure, ordinarily correct IBE whose efficiently recognizable identity space contains every verification key output by $\mathrm{SGen}$ and whose message space contains every valid label;
--   4. $P$ is an efficient secure PRF on the identity space with outputs of the extraction-tape length (stable extraction).
--
--   Then the signed construction (4.3) satisfies $\mathrm{IND}^{ad}_{\mathcal F_q}$ security, with ordinary correctness:
--   $$\mathrm{Signed}_q\in\mathrm{Sec}^{ad}(q).$$
--
--   The compiler protects only the public observation $q(m)$; it reaches adaptive $q$-security from CPA-level components, which is the intermediate security class the paper constructs.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: Sec^t(q) = Sec^t(F_q), F_q = {g ∘ q : g an admissible circuit / efficient public postprocessing} → SecM t M (famObs q); reason: the published famObs is the class of §2.3, p.14
--   - encoding: PPT primitives (R, L, I, P, S, N, q, samplers) → separate efficiency hypotheses (IsSchemeM, IsEfficient, IsPublic, IsObsMap); reason: the paper's PPT convention; the reductions run these algorithms
--   - reading: IBE extraction is stable per identity, using a secure PRF → the compiler derives the extraction tape PRF_k(id) with k in the secret key; P is a secure PRF on the identity space with outputs of length r_ext(λ); reason: §4.2, p.24 and Lemma 2, p.31
--   - reading: identities include the identities the compiler uses; the IBE message space contains every valid q-label → hypotheses on the identity space Id and the message space Ym of I; reason: §4.2, p.24 ('Its identities include a canonical, injective encoding of one-time verification keys; its message space contains every valid q-label')
--   - reading: a public identity space I_λ; malformed encodings are rejected → Id is efficiently recognizable and a ciphertext whose identity is outside Id_λ is malformed (⊥); reason: App. A.3, p.31 ('a public identity space Iλ'); decryption 'Reject malformed encodings', p.25; without the test the IBE and PRF reductions could not answer queries on identities outside I_λ
--   - encoding: ciphertext tuples and malformed encodings → canonical tuple codes; malformed = not the code of a tuple of the right length; reason: an unambiguous canonical encoding, p.24
--   - reading: Theorem 6's list of assumptions → adds correctness of the one-time signature (Definition 14); reason: the theorem takes ordinary correctness from Lemma 1, p.25, which assumes 'correctness of the one-time signature'
--   - encoding: the common message space → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 6, p.26; (4.3), pp.24–25; Lemma 1, p.25

import Mathlib
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_INDCPAM
import Definitions.Def_RestrictedDec_Supplement_signedCHK
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 6** (the signed CHK compiler is adaptively `q`-secure). Let `M` be a common message
space and `q` a public observation with `Valid_q`, `Rep_q`. Let `R` be an efficient, IND-CPA-secure,
ordinarily correct residual scheme over `M`; `S` an efficient, correct, strongly unforgeable
one-time signature; `I` an efficient, selective-identity IND-CPA-secure, ordinarily correct IBE
whose identity space contains every verification key output by `SGen` and whose message space
contains every valid label; and `P` an efficient secure PRF on the identity space with outputs of
the extraction-coin length. Then the signed construction (4.3) is in `Sec^ad(q)`, with ordinary
correctness.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 6, p.26; construction
(4.3), pp.24–25; Lemma 1, p.25; Definitions 2, 3, 5, 6, 7, 13, 14. -/
theorem theorem_6 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M) (o : Obs) (ho : o.IsPublic M)
    (R : PKE) (hR : IsSchemeM M R) (hRcpa : INDCPAM M R) (hRcor : CorrectM M R)
    (S : OTS) (hS : S.IsEfficient) (hSsuf : S.SUF) (hScor : S.Correct)
    (I : IBE) (Id Ym : ℕ → Str → Prop) (hI : I.IsEfficient)
    (hIdrec : Recognizable Id)
    (hId : ∀ (lam : ℕ) (r : Fin (S.keyCoins lam) → Bool), Id lam (S.gen lam r).2)
    (hYm : ∀ (lam : ℕ) (y : Str), o.valid lam y = true → Ym lam y)
    (hIsec : I.SelINDCPA Id Ym) (hIcor : I.Correct Id Ym)
    (P : PRF) (hPlen : ∀ lam, P.outLen lam = I.extCoins lam) (hP : P.IsEfficient Id)
    (hPsec : P.Secure Id) :
    SecM .ad M (famObs o.q) (signedCHK M Id o R I P S) := by sorry

end Supplement

end RestrictedDec
