-- Prove2me | Theorems.Thm_RestrictedDec_cca_implies_functional
-- name    : RestrictedDec.cca_implies_functional
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:56:37.569971+00:00
-- url     : https://prove2.me/theorems/a6d3684e-4bde-476d-ad63-26d8753a63e4
-- title:
--   §3.1 — CCA1 implies every $\mathrm{Sec}^{na}(\mathcal F)$, CCA2 implies every $\mathrm{Sec}^{ad}(\mathcal F)$
-- statement:
--   Let $\mathcal F$ be a valid family of permitted functions and $\Pi$ an efficient scheme over $\{0,1\}^{n(\lambda)}$.
--
--   1. If $\Pi$ is IND-CCA1 secure, then $\Pi\in\mathrm{Sec}^{na}(\mathcal F)$.
--   2. If $\Pi$ is IND-CCA2 secure, then $\Pi\in\mathrm{Sec}^{ad}(\mathcal F)$.
--
--   Full decryption simulates every functional answer, and an admissible query on the exact adaptive challenge is answered by the common value $F(m_0)=F(m_1)$ without decrypting. In the proof of Corollary 2 this is how both witnesses inherit security from the underlying CCA scheme.
--
--   Differences from the source:
--   - reading: public-key encryption scheme over {0,1}^{n(λ)} → PKE with PKE.IsScheme n (polynomial-time algorithms, Dec into M_⊥); reason: App. A.1, p.29 and the efficiency of PKE schemes; kept apart from Sec
--   - reading: IND-CCA1 / IND-CCA2 → INDCCA1 = Sec^na(𝓕_id), INDCCA2 = Sec^ad(𝓕_id); reason: §2.2, p.14: the requirements coincide, including ordinary correctness
--   - reading: every PPT adversary → every uniform reactive machine with a polynomial-time step function and polynomial bounds on coins, state, moves and activations; reason: the paper's adversaries are uniform (p.15 'a single PPT attack', p.28 'a uniform adversary')
--   - encoding: messages, keys, ciphertexts, pairs (β, c), positions in [n] → bit strings Str, (β, c) as β :: c, ⊥ as none, positions numbered from 1; reason: Lean convention; same instances
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §3.1, p.16

import Mathlib
import Definitions.Def_RestrictedDec_PKE_IsScheme
import Definitions.Def_RestrictedDec_INDCCA2
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- **Full decryption simulates every functional answer** (§3.1, p.16). For every valid family
`𝓕` of permitted functions and every efficient scheme `P` over `{0,1}^{n(λ)}`, IND-CCA1 security
implies `Sec^na(𝓕)` and IND-CCA2 security implies `Sec^ad(𝓕)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §3.1, p.16 ("Full decryption
can simulate every functional answer. … Thus CCA1 security implies every pre-challenge
functional-decryption requirement, and CCA2 security implies every adaptive one."). -/
theorem cca_implies_functional (n : ℕ → ℕ) (F : Family) (hF : F.Valid n) (P : PKE)
    (hP : P.IsScheme n) :
    (INDCCA1 n P → Sec .na n F P) ∧ (INDCCA2 n P → Sec .ad n F P) := by sorry

end RestrictedDec
