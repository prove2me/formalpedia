-- Prove2me | Theorems.Thm_SeededShannon_theorem_A_1
-- name    : SeededShannon.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T05:22:43.614648+00:00
-- url     : https://prove2.me/theorems/b9bc39bc-8938-4958-9b45-6baea71bd8dd
-- title:
--   Theorem A.1 — recoverable embeddings and injective one-way functions give evasive obfuscation
-- statement:
--   Suppose there is a recoverable embedding $\Pi_{\mathrm{Emb}}$ (Definition 5.4) for a family $\{\mathcal F_{\lambda,n}\}_{n\ge N_{\min}(\lambda)}$ with minimum input length $N_{\min}$, and suppose injective one-way functions exist. Then there is a distributional evasive obfuscator (Definition 5.1) for the same family, with the same minimum input length and supported lengths.
--
--   Theorems 5.2 and 5.3 follow from the embedding theorems 5.5 and 5.6 through this transformation.
--
--   **Formalization Note** Injective one-way functions are the published `NoisyOWMPC.KeyedFamily.IsInjOWF`.
--
--   Differences from the source:
--   - generalization: injective one-way functions, F : {0,1}^n → {0,1}^{ℓowf} unkeyed and injective (Def. 3.2) → a keyed family injective except with negligible probability over the key (published `NoisyOWMPC.KeyedFamily.IsInjOWF`); reason: a weaker hypothesis: an unkeyed injective OWF is such a family with key length 0; this is the form given by iO + OWF [BPW16] (platform item NoisyOWMPC.theorem_3_4)
--   - generalization: supported lengths n ≥ N_min(λ) with an efficiently checkable restriction (Definition 5.1) → n ≥ N_min(λ) with an arbitrary restriction supp; reason: more instances; for an efficiently checkable restriction it is the paper's statement
--   - encoding: a deterministic polynomial-time map from seeds σ to descriptions of f_σ → the field func : seeds → functions, with one polynomial-time machine computing f_σ(x) from (1^λ, 1^n, σ, x) for every seed returned by GenProg; reason: with no fixed description language, a description is anything that evaluates f_σ in polynomial time; Construction A.2's seed σ = (pp, u) evaluates through SampleFunc
--   - reading: efficient / polynomial-time adversaries → nonuniform polynomial-size deterministic circuit families (`Distinguisher`, `CircFamily`); schemes are uniform machines; reason: Def. 3.1 allows non-uniform adversaries and the reductions hard-wire keys, so one nonuniform class is used throughout; a randomized adversary is matched by its best coins
--   - encoding: for every polynomially bounded n (every polynomial P) → pointwise clauses for all n ≥ N_min(λ); probabilistic clauses for every bound n ≤ (λ+2)^c; reason: the pointwise clauses hold at each length, and every polynomial is bounded by some (λ+2)^c
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem A.1, p.61 (PDF p.64)

import Mathlib
import Definitions.Def_NoisyOWMPC_KeyedFamily
import Definitions.Def_SeededShannon_RecEmb
import Definitions.Def_SeededShannon_EvObf

set_option autoImplicit false

namespace SeededShannon

open NoisyOWMPC

/-- **Theorem A.1** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission (manuscript sha256
52f4b606…a769709), Theorem A.1, p.61): if there is a recoverable embedding (Definition 5.4) for a
family `{F_{λ,n}}` with minimum input length `N_min`, and injective one-way functions exist, then
there is a distributional evasive obfuscator (Definition 5.1) for the same family, with the same
minimum input length and supported lengths.

**Formalization Note** Injective one-way functions are the published keyed families
`NoisyOWMPC.KeyedFamily.IsInjOWF` (injective except with negligible probability over the key). The
restriction `supp` on supported lengths is arbitrary. -/
theorem theorem_A_1 (Nmin : ℕ → ℕ) (supp : ℕ → ℕ → Prop)
    (F : (lam n : ℕ) → Set ((Fin n → Bool) → Bool))
    (hEmb : ∃ E : RecEmb, E.IsRecEmb Nmin supp F) (hInj : ∃ G : KeyedFamily, G.IsInjOWF) :
    ∃ O : EvObf, O.IsEvObf Nmin supp F := by sorry

end SeededShannon
