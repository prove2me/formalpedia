-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_9
-- name    : RestrictedDec.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:42:32.839859+00:00
-- url     : https://prove2.me/theorems/60859649-ad3a-41cb-bd01-e0ab61f618cd
-- title:
--   Theorem 9 — the probe-augmented Naor–Yung scheme $\hat\Gamma_q$ is in $\mathrm{Sec}^{na}(q)\setminus\mathrm{Sec}^{na}(r)$; $\mathrm{Sec}^{na}(r)\subsetneq\mathrm{Sec}^{na}(q)$
-- statement:
--   Under the assumptions of Theorem 8, let $r$ be a public observation, let $\mathrm{dflt}(\lambda)\in M_\lambda$ be an efficiently computable fixed valid default message, and let $W$ be a uniform PPT witness sampler that outputs distinct valid equal-length $u,v$ with
--   $$q(u)=q(v),\qquad r(u)\neq r(v)\tag{B.3}$$
--   with non-negligible probability on infinitely many security parameters. Then the scheme $\hat\Gamma_q$
--
--   1. is secure against pre-challenge $\mathcal F_q$-decryption queries: $\hat\Gamma_q\in\mathrm{Sec}^{na}(q)$;
--   2. is insecure against pre-challenge $\mathcal F_r$-decryption queries: $\hat\Gamma_q\notin\mathrm{Sec}^{na}(r)$;
--   3. hence, whenever $q$ is efficiently recoverable from $r$, the pre-challenge inclusion is strict:
--   $$\mathrm{Sec}^{na}(r)\subsetneq\mathrm{Sec}^{na}(q).$$
--
--   Probes decrypt to $u$ or $v$, which the $q$-oracle cannot tell apart but the $r$-oracle can, so a finer oracle reads the whole secret key before the challenge.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: Sec^t(q) = Sec^t(F_q), F_q = {g ∘ q : g an admissible circuit / efficient public postprocessing} → SecM t M (famObs q); reason: the published famObs is the class of §2.3, p.14
--   - encoding: PPT primitives (R, L, I, P, S, N, q, samplers) → separate efficiency hypotheses (IsSchemeM, IsEfficient, IsPublic, IsObsMap); reason: the paper's PPT convention; the reductions run these algorithms
--   - reading: efficient recognition of valid plaintexts; perfect completeness of the NIZK → hypotheses Recognizable M and N.Complete; reason: standing assumptions of App. B.1, p.35 ('efficient recognition of valid plaintexts'; 'Both constructions require perfect completeness')
--   - encoding: a label scheme L encrypting ℓ(λ)-bit strings; the label length ℓ(λ) of q → L a PKE efficient and IND-CPA over {0,1}^{ℓ(λ)}, with ℓ the length of q on M_⊥; reason: App. B.1, p.35
--   - encoding: Coins_L, a publicly recognizable set of allowed label randomness → every encryption coin vector of L; r ∈ Coins_L in the relation is |r| = encCoins_L(λ); reason: honest label encryption draws its coins uniformly from all coin vectors, so they are all allowed
--   - encoding: the ciphertext and statement tuples; malformed ciphertexts → canonical tuple codes; the secret key also stores pk₀, pk₁, crs; reason: decryption needs them to form and verify the statement
--   - reading: a simulator producing accepting proofs for well-formed statements → simulated-proof acceptance (Definition 11) for every well-formed statement; reason: App. A.4, p.34
--   - reading: probes (1, j) with 1 ≤ j ≤ L for an L-bit encoding s₁⋯s_L of the secret key; ⊥ otherwise → every j is a probe, s is the self-delimiting code of the key followed by zeros; reason: the paper fixes no public length L; a key-dependent L would let the set of probes leak |sk|; the convention of the published RestrictedDec.probeScheme
--   - encoding: the same fixed valid default message → a parameter dflt with dflt(λ) ∈ M_λ computed by a polynomial-time machine; reason: p.38
--   - encoding: a PPT witness sampler succeeding with nonnegligible probability on infinitely many security parameters → a uniform PPT Sampler whose success probability for (B.3) is not negligible; reason: a function is non-negligible iff it exceeds some inverse polynomial infinitely often
--   - reading: whenever q is efficiently recoverable from r, the corresponding pre-challenge security inclusion is strict → Recoverable M q r → SecSubsetneq .na M (famObs r) (famObs q); reason: asymptotic strictness, §2.3, p.15
--   - encoding: the common message space → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 9, p.38

import Mathlib
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_INDCPAM
import Definitions.Def_RestrictedDec_Supplement_kcFail
import Definitions.Def_RestrictedDec_Supplement_SecSubsetneq
import Definitions.Def_RestrictedDec_Supplement_Sampler
import Definitions.Def_RestrictedDec_Supplement_nyPre
import Definitions.Def_RestrictedDec_Supplement_nyProbe
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 9** (pre-challenge finer-observation separation by the probe-augmented Naor–Yung
scheme). Under the assumptions of Theorem 8, let `r` be a public observation and `W` a uniform PPT
witness sampler that outputs distinct valid equal-length `u, v` with `q(u) = q(v)` and
`r(u) ≠ r(v)` (B.3) with non-negligible probability on infinitely many security parameters, and let
`dflt(λ) ∈ M_λ` be an efficiently computable fixed valid default message. Then the scheme `Γ̂_q`
1. is secure against pre-challenge `𝓕_q`-decryption queries: `Γ̂_q ∈ Sec^na(q)`;
2. is insecure against pre-challenge `𝓕_r`-decryption queries: `Γ̂_q ∉ Sec^na(r)`;
3. hence, whenever `q` is efficiently recoverable from `r`, `Sec^na(r) ⊊ Sec^na(q)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 9, p.38; (B.3) and the
scheme `Γ̂_q`, p.38. -/
theorem theorem_9 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M) (hMrec : Recognizable M)
    (o : Obs) (ho : o.IsPublic M) (ℓ : ℕ → ℕ)
    (hℓ : ∀ lam (x : Option Str), (∀ m, x = some m → M lam m) → (o.q lam x).length = ℓ lam)
    (R : PKE) (hR : IsSchemeM M R) (hRcpa : INDCPAM M R) (hRcor : CorrectM M R)
    (L : PKE) (hL : IsSchemeM (fun lam y => y.length = ℓ lam) L)
    (hLcpa : INDCPAM (fun lam y => y.length = ℓ lam) L) (hLkc : KeywiseCorrect L ℓ)
    (N : NIZK) (hN : N.IsEfficient) (hNc : N.Complete (relB1 L o)) (hNs : N.Sound (relB1 L o))
    (hNzk : N.ZK (relB1 L o)) (hNacc : N.SimAccept wfB1)
    (r : ℕ → Option Str → Str) (hr : IsObsMap M r)
    (W : Sampler) (hW : W.IsEfficient)
    (hWs : ¬ NoisyOWMPC.Negligible (W.succ fun lam u v => M lam u ∧ M lam v ∧ u ≠ v ∧
      u.length = v.length ∧ o.q lam (some u) = o.q lam (some v) ∧ r lam (some u) ≠ r lam (some v)))
    (dflt : ℕ → Str)
    (hdflt : (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam, f (encNat lam) = dflt lam) ∧
      ∀ lam, M lam (dflt lam)) :
    SecM .na M (famObs o.q) (nyProbe (nyPre M o R L N) W M o.q dflt) ∧
    ¬ SecM .na M (famObs r) (nyProbe (nyPre M o R L N) W M o.q dflt) ∧
    (Recoverable M o.q r → SecSubsetneq .na M (famObs r) (famObs o.q)) := by sorry

end Supplement

end RestrictedDec
