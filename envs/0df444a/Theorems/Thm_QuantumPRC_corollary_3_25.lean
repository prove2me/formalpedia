-- Prove2me | Theorems.Thm_QuantumPRC_corollary_3_25
-- name    : QuantumPRC.corollary_3_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:48.925865+00:00
-- url     : https://prove2.me/theorems/a6f68b4d-4f42-4273-9435-9138ab1d3649
-- title:
--   Corollary 3.25 — secret-key PRCs imply PRFs and PRPs
-- statement:
--   If, for some efficient polynomial lengths $n,m$ and some classical noise channel $\mathcal E$, an $(n,m)$ secret-key PRC robust to $\mathcal E$ exists, then:
--
--   1. for all efficient polynomial lengths $n',m'$ there is a PRF $F:\{0,1\}^\lambda\times\{0,1\}^{n'(\lambda)}\to\{0,1\}^{m'(\lambda)}$ secure against quantum queries (Definition 3.17), and
--   2. for every efficient polynomial length $n'$ there is a PRP on $\{0,1\}^{n'(\lambda)}$ secure against quantum queries to the permutation and its inverse (Definition 3.18).
--
--   The paper derives this from the fact that secret-key PRCs give IND-CPA-secure secret-key encryption; it is used to obtain the PRFs and PRPs inside Constructions 6.5 and 7.2.
--
--   Differences from the source:
--   - reading: if secret-key PRCs exist, then PRFs and PRPs exist → if an (n, m) secret-key PRC robust to some noise channel exists for some EffPoly n, m, then PRFs exist for all EffPoly lengths and PRPs for all EffPoly lengths; reason: the usual meaning of existence of a primitive; Constructions 6.5 and 7.2 need PRFs and PRPs of several lengths
--   - generalization: n, m (or nL, nP, ℓ, r, m) are polynomials → they are EffPoly lengths: polynomially bounded and computable from 1^λ in polynomial time; reason: every integer-valued polynomial is such a length, so the Lean statement contains the printed one (paper.md decision 2)
--   - reading: QPT algorithm / QPT adversary (no machine model given) → uniform families of Clifford+T oracle circuits printed by a polynomial-time Turing machine; PPT algorithms are polynomial-time functions of polynomially many fair coins; reason: the paper fixes no model; this one covers adaptive and reference-entangled queries and is used on both sides of every implication (paper.md decision 3)
--   - reading: query access to PRFs and PRPs (not specified in Definitions 3.17, 3.18) → quantum oracle access |x⟩|y⟩ ↦ |x⟩|y ⊕ g(x)⟩ as in (82), with separate oracles for π_k and π_k⁻¹; reason: the post-quantum notion the paper uses in §7.2 ([Zha12], [Zha25])
--   - encoding: secret-key PRCs robust to some noise channel E → E is given by transition probabilities forming a Markov kernel (IsCNoise E); reason: the type of a classical noise channel in Definitions 3.6 and 3.24; excludes only maps that are not channels
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Corollary 3.25, p.24; Definitions 3.17, 3.18, 3.24

import Mathlib
import Definitions.Def_QuantumPRC_SKPRC
import Definitions.Def_QuantumPRC_PRF

namespace QuantumPRC

/-- **Corollary 3.25** (secret-key PRCs imply PRFs and PRPs). Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), Corollary 3.25, p.24: "If secret-key PRCs exist, then PRFs and PRPs exist."

**Formalization Note.** "Secret-key PRCs exist": for some `EffPoly` lengths `n, m` and some classical
noise channel `E`, an `(n, m)` secret-key PRC robust to `E` exists (Definition 3.24). "PRFs and PRPs
exist": for all `EffPoly` lengths, a PRF (Definition 3.17) and a PRP (Definition 3.18), both secure
against quantum queries. -/
theorem corollary_3_25 :
    (∃ (n m : ℕ → ℕ) (E : CNoise m) (S : SKPRC n m),
        EffPoly n ∧ EffPoly m ∧ IsCNoise E ∧ S.IsPRC E) →
      (∀ n m : ℕ → ℕ, EffPoly n → EffPoly m → ∃ F : PRF n m, F.IsPRF) ∧
      (∀ n : ℕ → ℕ, EffPoly n → ∃ P : PRP n, P.IsPRP) := by sorry

end QuantumPRC
