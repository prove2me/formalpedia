-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_lemma_12
-- name    : TrapdoorHCF.CCA2.Supplement.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:36.747114+00:00
-- url     : https://prove2.me/theorems/2dbce145-6eac-4127-b6cc-391f491ff0c3
-- title:
--   Lemma 12 — statistical lossiness of the Section C.2 LTDHF
-- statement:
--   Let $l:\mathbb N\to\mathbb N$ and let $P$ be a lossy public-key encryption scheme that satisfies ciphertext lossiness for messages in $\{0,1\}^{l(\lambda)}$ (Definition 7). Then the Section C.2 function $\mathrm{LTDHF}_l(P)$, with input $x=m\Vert r$, $\mathrm{Eval}(pk,x)=\mathrm{Enc}(pk,m;r)$ and $\mathrm{hEval}(pk,x)=m$, is statistically lossy: there is a negligible $\varepsilon$ such that for every $\lambda$ and every lossy key $pk$ in the support of $\mathrm{Gen}_{lossy}(1^\lambda)$,
--
--   $$\Delta\bigl((\mathrm{Eval}(pk,X),\mathrm{hEval}(pk,X)),\ (\mathrm{Eval}(pk,X),U)\bigr)\le\varepsilon(\lambda),$$
--
--   with $X$ uniform on $D_\lambda$ and $U\leftarrow\{0,1\}^{l(\lambda)}$ independent. This is the statistical-lossiness part of Theorem 11.
--
--   Differences from the source:
--   - generalization: the Section C.2 standing assumption: a perfectly correct and secure (efficient) lossy PKE with message space {0,1}^{l(lambda)} → only ciphertext lossiness of P for messages of length l(lambda) is assumed; no correctness, mode indistinguishability, efficiency or public length; reason: the lemma states exactly this hypothesis and is a statement about laws; every scheme of Section C.2 satisfies it
--   - encoding: every lossy public key in Supp(KGen_los(1^lambda)) → losKeyGen lambda r for every lossy key coin vector r; reason: the same set of keys
--   - encoding: statistical distance (1/2) sum over omega of |Pr[X = omega] - Pr[Y = omega]| → (1/2) times the real tsum over all outcomes of |p(omega) - q(omega)| for PMFs on an arbitrary type; reason: the series is absolutely summable for PMFs, so this is the same number; no finiteness of the outcome space is assumed
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Lemma 12, p.52 (proof p.52), for the construction of Section C.2, p.50

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_Lossy
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Lemma 12, p.52: statistical lossiness of the Section C.2 LTDHF from ciphertext lossiness. -/
theorem lemma_12 :
    ∀ (l : ℕ → ℕ) (P : LPKE), P.CiphertextLossy l → (ltdhfOfLPKE l P).StatLossy l := by sorry

end TrapdoorHCF.CCA2.Supplement
