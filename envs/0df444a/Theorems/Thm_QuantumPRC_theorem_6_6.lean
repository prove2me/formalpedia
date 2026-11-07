-- Prove2me | Theorems.Thm_QuantumPRC_theorem_6_6
-- name    : QuantumPRC.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:42.559807+00:00
-- url     : https://prove2.me/theorems/ca74621d-990d-4210-9d44-57f0ec6c1ce2
-- title:
--   Theorem 6.6 — Construction 6.5 is a PRFC
-- statement:
--   Let $n,m,\ell$ be efficient polynomial lengths with $n(\lambda)=\omega(\log\lambda)$ and $n(\lambda)\le m(\lambda)$ for all $\lambda$. Let $(\mathsf{PRC.KeyGen},\mathsf{PRC.Enc},\mathsf{PRC.Dec})$ be an $(n,m)$ secret-key PRC robust to a classical noise channel $\mathcal E$ whose encoder uses an $\ell(\lambda)$-bit random string, let $\Pi$ be a PRP on $n$ bits and let $F:\{0,1\}^\lambda\times\{0,1\}^{n(\lambda)}\to\{0,1\}^{\ell(\lambda)}$ be a PRF. Then Construction 6.5,
--
--   $$
--   \mathrm{Enc}((\mathsf{sk}',k,k',r),x)=\mathsf{PRC.Enc}(\mathsf{sk}',\pi_k(x);f_{k'}(x)\oplus r),
--   $$
--
--   with decoder $c\mapsto\pi_k^{-1}(\mathsf{PRC.Dec}(\mathsf{sk}',c))$ (and $0^{n}$ on $\bot$), is an $(n,m)$ PRFC robust to $\mathcal E$ (Definition 6.1): it is efficient, robust to $\mathcal E$, and pseudorandom against quantum queries.
--
--   PRFCs are the classical inner codes of the PRIC construction; their pseudorandomness under quantum queries is what Lemma 7.11 needs.
--
--   Differences from the source:
--   - generalization: n, m (or nL, nP, ℓ, r, m) are polynomials → they are EffPoly lengths: polynomially bounded and computable from 1^λ in polynomial time; reason: every integer-valued polynomial is such a length, so the Lean statement contains the printed one (paper.md decision 2)
--   - reading: QPT algorithm / QPT adversary (no machine model given) → uniform families of Clifford+T oracle circuits printed by a polynomial-time Turing machine; PPT algorithms are polynomial-time functions of polynomially many fair coins; reason: the paper fixes no model; this one covers adaptive and reference-entangled queries and is used on both sides of every implication (paper.md decision 3)
--   - encoding: E is a noise channel → E is given by transition probabilities forming a Markov kernel (IsCNoise E); reason: the type of a classical noise channel in Definition 3.24
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 6.6 and Construction 6.5, p.34; Definition 6.1, p.33

import Mathlib
import Definitions.Def_QuantumPRC_PRFC

namespace QuantumPRC

/-- **Theorem 6.6** (Construction 6.5 is a PRFC). Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
Theorem 6.6, p.34: "If `n(λ) = ω(log λ)` and `n(λ) ≤ m(λ)`, then `(KeyGen, Enc, Dec)` in Construction 6.5 is
an `(n, m)` PRFC robust to `E`."

Construction 6.5, p.34: "Let `n, m, ℓ : ℕ → ℕ` be polynomials. Let `(PRC.KeyGen, PRC.Enc, PRC.Dec)` be an
`(n, m)` secret-key PRC robust to a noise channel `E` such that `PRC.Enc` uses an `ℓ(λ)`-bit string as
internal randomness. Let `Π : {0,1}^λ × {0,1}^{n(λ)} → {0,1}^{n(λ)}` be a PRP […]. Let
`F : {0,1}^λ × {0,1}^{n(λ)} → {0,1}^{ℓ(λ)}` be a PRF."

**Formalization Note.** "Polynomials" are `EffPoly` lengths; `ℓ = S.ec`. -/
theorem theorem_6_6 (n m : ℕ → ℕ) (hn : EffPoly n) (hm : EffPoly m) (S : SKPRC n m)
    (hℓ : EffPoly S.ec) (Pm : PRP n) (F : PRF n S.ec) (E : CNoise m) (hE : IsCNoise E)
    (hS : S.IsPRC E) (hP : Pm.IsPRP) (hF : F.IsPRF)
    (hω : SuperLog fun lam => (n lam : ℝ)) (hnm : ∀ lam, n lam ≤ m lam) :
    (construction65 S Pm F).IsPRFC E := by sorry

end QuantumPRC
