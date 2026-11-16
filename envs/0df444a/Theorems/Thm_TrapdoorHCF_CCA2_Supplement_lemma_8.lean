-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_lemma_8
-- name    : TrapdoorHCF.CCA2.Supplement.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:46:33.814127+00:00
-- url     : https://prove2.me/theorems/47529975-01fb-43d2-9c3c-4f7821c3e2d7
-- title:
--   Lemma 8 — ciphertext lossiness of the Section C.1 scheme
-- statement:
--   Let $l:\mathbb N\to\mathbb N$ and let $T$ be a lossy trapdoor hardcore function that is statistically lossy with hardcore length $l(\lambda)$ (Definition 15). Then the Section C.1 scheme $\mathrm{LPKE}(T)$, whose encryption is $\mathrm{Enc}(pk,m;X)=(\mathrm{Eval}(pk,X),\mathrm{hEval}(pk,X)\oplus m)$ with $X\leftarrow D_\lambda$, is ciphertext lossy: there is a negligible $\varepsilon$ such that for every $\lambda$, every lossy public key $pk$ in the support of $\mathrm{KGen}_{los}(1^\lambda)$ and all messages $m_0,m_1\in\{0,1\}^{l(\lambda)}$,
--
--   $$\Delta\bigl(\mathrm{Enc}(pk,m_0;X_0),\ \mathrm{Enc}(pk,m_1;X_1)\bigr)\le\varepsilon(\lambda),$$
--
--   with $X_0,X_1\leftarrow D_\lambda$ independent. This is the ciphertext-lossiness part of Theorem 10.
--
--   Differences from the source:
--   - generalization: the Section C.1 standing assumption: a perfectly correct and secure (efficient) LTDHF → only statistical lossiness of T is assumed; no correctness, mode indistinguishability or efficiency; reason: the lemma is a statement about laws under lossy keys and the proof uses only Definition 15; every LTDHF of the source satisfies the weaker hypothesis
--   - reading: Enc(pk, m0; X0) ≈s Enc(pk, m1; X1) for every lambda, lossy key and messages → one negligible bound epsilon(lambda) uniform over lambda, lossy keys and messages, i.e. Definition 7 ciphertext lossiness; reason: SUPPLEMENT.md decision S4: this is what the proof gives (twice the Definition 15 bound), what Theorem 10 needs, and the stronger of the possible readings of a per-key ≈s
--   - generalization: uniform sampling from efficiently recognizable input spaces D_lambda → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: base paper.md decision 5; every source input space is an instance, so the hypothesis class only grows; the constructions and experiments use only sampling
--   - encoding: every lossy public key in Supp(KGen_los(1^lambda)) → losKeyGen lambda r for every lossy key coin vector r; reason: the same set of keys
--   - encoding: statistical distance (1/2) sum over omega of |Pr[X = omega] - Pr[Y = omega]| → (1/2) times the real tsum over all outcomes of |p(omega) - q(omega)| for PMFs on an arbitrary type; reason: the series is absolutely summable for PMFs, so this is the same number; no finiteness of the outcome space is assumed
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Lemma 8, p.49 (proof p.49), for the construction of Section C.1, pp.47–48

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_Lossy
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Lemma 8, p.49: ciphertext lossiness of the Section C.1 scheme from statistical lossiness. -/
theorem lemma_8 :
    ∀ (l : ℕ → ℕ) (T : LTDHF), T.StatLossy l → (lpkeOfLTDHF T).CiphertextLossy l := by sorry

end TrapdoorHCF.CCA2.Supplement
