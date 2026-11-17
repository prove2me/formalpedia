-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_7
-- name    : RestrictedDec.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:40:37.457075+00:00
-- url     : https://prove2.me/theorems/6413b936-73c4-4026-a4e0-6c9bff6da323
-- title:
--   Theorem 7 — the signed CHK compiler is in $\mathrm{Sec}^{ad}(q)\setminus\mathrm{Sec}^{ad}(r)$ when $q=T\circ r$
-- statement:
--   Under the assumptions of Theorem 6, let $r$ be a public observation and suppose $q=T\circ r$ for an efficient map $T$. If a uniform PPT sampler, run independently of the generated keys, always outputs valid messages $u_0,u_1$ of equal length with
--   $$q(u_0)=q(u_1),\qquad r(u_0)\neq r(u_1),$$
--   then the signed construction $\Pi$ of (4.3) satisfies
--   $$\Pi\in\mathrm{Sec}^{ad}(q)\setminus\mathrm{Sec}^{ad}(r).$$
--
--   The signature binds the label ciphertext to the residual one only under the original verification key; re-wrapping the challenge residual under a fresh key and a fresh encryption of the common label is harmless for the $q$-oracle but exposes the residual message to a finer oracle.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: Sec^t(q) = Sec^t(F_q), F_q = {g ∘ q : g an admissible circuit / efficient public postprocessing} → SecM t M (famObs q); reason: the published famObs is the class of §2.3, p.14
--   - encoding: PPT primitives (R, L, I, P, S, N, q, samplers) → separate efficiency hypotheses (IsSchemeM, IsEfficient, IsPublic, IsObsMap); reason: the paper's PPT convention; the reductions run these algorithms
--   - reading: IBE extraction is stable per identity, using a secure PRF → the compiler derives the extraction tape PRF_k(id) with k in the secret key; P is a secure PRF on the identity space with outputs of length r_ext(λ); reason: §4.2, p.24 and Lemma 2, p.31
--   - reading: identities include the identities the compiler uses; the IBE message space contains every valid q-label → hypotheses on the identity space Id and the message space Ym of I; reason: §4.2, p.24 ('Its identities include a canonical, injective encoding of one-time verification keys; its message space contains every valid q-label')
--   - reading: a public identity space I_λ; malformed encodings are rejected → Id is efficiently recognizable and a ciphertext whose identity is outside Id_λ is malformed (⊥); reason: App. A.3, p.31 ('a public identity space Iλ'); decryption 'Reject malformed encodings', p.25; without the test the IBE and PRF reductions could not answer queries on identities outside I_λ
--   - encoding: ciphertext tuples and malformed encodings → canonical tuple codes; malformed = not the code of a tuple of the right length; reason: an unambiguous canonical encoding, p.24
--   - reading: Theorem 6's list of assumptions → adds correctness of the one-time signature (Definition 14); reason: Lemma 1, p.25, and the attack's acceptance of the re-signed ciphertext, p.27
--   - encoding: r a public observation; q = T ∘ r for an efficient map T → IsObsMap M r and Recoverable M q r (T polynomial-time on (1^λ, r(x))); reason: §2.3, p.14
--   - encoding: efficiently found valid messages u₀, u₁ of equal length, sampled independently of the generated keys → a uniform PPT sampler (no key input) every output of which has the stated property; reason: 'sampled independently of the generated keys', p.27
--   - encoding: the common message space → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 7, p.27

import Mathlib
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_INDCPAM
import Definitions.Def_RestrictedDec_Supplement_Sampler
import Definitions.Def_RestrictedDec_Supplement_signedCHK
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 7** (adaptive finer-observation separation for the signed CHK compiler). Under the
assumptions of Theorem 6, let `r` be a public observation with `q = T ∘ r` for an efficient map
`T`. If a uniform PPT sampler, run independently of the keys, always outputs valid messages
`u₀, u₁` of equal length with `q(u₀) = q(u₁)` and `r(u₀) ≠ r(u₁)`, then the signed construction
`Π` satisfies `Π ∈ Sec^ad(q) \ Sec^ad(r)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 7, p.27. -/
theorem theorem_7 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M) (o : Obs) (ho : o.IsPublic M)
    (R : PKE) (hR : IsSchemeM M R) (hRcpa : INDCPAM M R) (hRcor : CorrectM M R)
    (S : OTS) (hS : S.IsEfficient) (hSsuf : S.SUF) (hScor : S.Correct)
    (I : IBE) (Id Ym : ℕ → Str → Prop) (hI : I.IsEfficient)
    (hIdrec : Recognizable Id)
    (hId : ∀ (lam : ℕ) (r : Fin (S.keyCoins lam) → Bool), Id lam (S.gen lam r).2)
    (hYm : ∀ (lam : ℕ) (y : Str), o.valid lam y = true → Ym lam y)
    (hIsec : I.SelINDCPA Id Ym) (hIcor : I.Correct Id Ym)
    (P : PRF) (hPlen : ∀ lam, P.outLen lam = I.extCoins lam) (hP : P.IsEfficient Id)
    (hPsec : P.Secure Id)
    (r : ℕ → Option Str → Str) (hr : IsObsMap M r) (hT : Recoverable M o.q r)
    (W : Sampler) (hW : W.IsEfficient)
    (hWout : ∀ lam (ρ : Fin (W.coins lam) → Bool),
      M lam (W.out lam ρ).1 ∧ M lam (W.out lam ρ).2 ∧
      (W.out lam ρ).1.length = (W.out lam ρ).2.length ∧
      o.q lam (some (W.out lam ρ).1) = o.q lam (some (W.out lam ρ).2) ∧
      r lam (some (W.out lam ρ).1) ≠ r lam (some (W.out lam ρ).2)) :
    SecM .ad M (famObs o.q) (signedCHK M Id o R I P S) ∧
      ¬ SecM .ad M (famObs r) (signedCHK M Id o R I P S) := by sorry

end Supplement

end RestrictedDec
