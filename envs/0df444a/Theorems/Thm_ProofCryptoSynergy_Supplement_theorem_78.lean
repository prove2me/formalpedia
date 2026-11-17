-- Prove2me | Theorems.Thm_ProofCryptoSynergy_Supplement_theorem_78
-- name    : ProofCryptoSynergy.Supplement.theorem_78
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:59:00.364507+00:00
-- url     : https://prove2.me/theorems/aea4f985-329a-43df-a42e-751e19512970
-- title:
--   Theorem 78 — under NP ⊄ BPP, iO and privately verifiable extractable WE do not both exist
-- statement:
--   Assume $\mathsf{NP}\not\subseteq\mathsf{BPP}$. Then at most one of the following holds:
--
--   1. indistinguishability obfuscation exists;
--   2. privately verifiable extractable witness encryption exists (one scheme with both properties).
--
--   It is a dichotomy: believing in iO and the worst-case hardness of NP rules out witness encryption that is both extractable and privately verifiable.
--
--   Differences from the source:
--   - reading: iO exists; witness encryption (Section 6) → polynomially secure iO (IsPolyIO) and polynomially secure WE for SAT (IsPolyWE); reason: Section 6 is the polynomial regime
--   - encoding: BPP (undefined in the paper) → L ∈ BPP iff (L, Lᶜ) ∈ promiseBPP (published); reason: standard definition
--   - reading: Definition 69: witnesses w ∈ {0,1}^{poly(n)} with (x, w) ∈ R_L → satisfying assignments with |w| ≤ |x|; reason: the SAT relation of the mission; every satisfiable formula has such a witness
--   - reading: Definition 67: for any polynomial q, q(n)-size A and x ∈ {0,1}ⁿ (every n) → for each q = n^c, for all sufficiently large n; reason: Definition 67 extends Definition 13, whose properties hold for large n; read for every n it forces Enc(x,0) and Enc(x,1) to be identically distributed for unsatisfiable x with |x| ≥ 2 (NP = coNP), and Lemma 75 (Item 1) only yields extraction for large n
--   - encoding: Pr_{b,Enc}[A(x, Enc(x,b)) = b] ≥ 1/2 + 1/q(n); PPT extractor E(x, A) → (Pr − 1/2)·n^c ≥ 1 with A reading padIn k (x ++ ct); extractor polynomial-time in |x| + |code A| with polynomially many coins; reason: no division; adversaries read strings as in the published Indist
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 78, p.57 (PDF 59)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_Supplement_NPNotBPP
import Definitions.Def_ProofCryptoSynergy_Supplement_PolyIOExists
import Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyWE

open KarpLiptonOM LaconicBarrier ProofCryptoSynergy

namespace ProofCryptoSynergy.Supplement

/-- **Theorem 78** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.57 (PDF 59)). Assume that `NP ⊄ BPP`. At most one of the following
holds.
* iO exists;
* privately verifiable extractable witness encryption exists.

**Formalization Note** Section 6 is the polynomial regime: iO is the polynomially secure `IsPolyIO`, witness
encryption the polynomially secure `IsPolyWE` for SAT, and one scheme is both privately verifiable and
extractable. -/
theorem theorem_78 :
    NPNotBPP →
      ¬ (PolyIOExists ∧ ∃ E : WEForSAT, IsPolyWE E ∧ PrivVerifiableWE E ∧ ExtractableWE E) := by sorry

end ProofCryptoSynergy.Supplement
