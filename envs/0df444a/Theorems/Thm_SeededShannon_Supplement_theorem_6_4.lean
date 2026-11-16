-- Prove2me | Theorems.Thm_SeededShannon_Supplement_theorem_6_4
-- name    : SeededShannon.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:44:48.26611+00:00
-- url     : https://prove2.me/theorems/31d3bf18-fb2c-478e-891d-e8b034bcb7ad
-- title:
--   Theorem 6.4 — selective computational correctness of Construction 6.1
-- statement:
--   Assume the primitives in Construction 6.1 satisfy their stated definitions. Then Construction 6.1 is a selectively $(p,L)$-correct seeded code in the sense of Definition 3.15, with the list bound
--   $$L=t\cdot L_{\mathrm{pprc}}(\lambda,\ell_{\mathrm{hash}})\cdot L_{\mathrm{bal}}(N)$$
--   of Lemma 6.2: for every efficient adversary $\mathcal A=(\mathcal A_1,\mathcal A_2)$, the experiment $\mathrm{ExpCorrect}^{(p)}(\mathcal A,\lambda)$ outputs $1$ with negligible probability, at every supported length $k_{\min}(\lambda)\le k\le 2^\lambda$. In particular, the adversary may evaluate both public programs on inputs of its choice before producing $y$. Its decoder is also $p$-sound, by the distance check of the decoding program, every encoding has length $N$, and its algorithms run in polynomial time.
--
--   This is the correctness theorem behind the list-decodable seeded codes at Shannon rate (Theorem 6.13) and the base code of Theorem 7.15.
--
--   **Formalization Note** The circuits obfuscated by Setup come from circuit builders: the statement holds for every polynomial-time builder that computes the two programs exactly at padded sizes at least some polynomial thresholds $S_E^0,S_D^0$ (which exist), with room for $L+1$ candidates in the decoder's output.
--
--   Differences from the source:
--   - generalization: Setup obfuscates circuits for the programs of Figs. 7 and 8, padded to common polynomial size → ∃ polynomial thresholds S₀_E, S₀_D such that every polynomial-time circuit builder computing the programs exactly at padded sizes ≥ S₀ works; reason: the paper's own compilation, padded large enough for the hybrid circuits, is one such builder
--   - generalization: a puncturable PRF and a puncturable τ-robust PRC → 1-puncturable (IsPPRF / IsPPRCAt with t = 1); reason: the construction punctures at the single point {h*}; a t-puncturable primitive with t ≥ 1 is 1-puncturable
--   - generalization: C the constant of Theorem 3.14 → any C > 0 with R < 1 − H(τ) − C√γ and a balanced code of rate ≥ 1 − H(τ) − C√γ; reason: the construction uses C only through this rate; Theorem 3.14's constant is one choice
--   - encoding: a selectively (p, L)-correct seeded code in the sense of Definition 3.15 (three efficient algorithms) … its decoder is also p-sound → SeededCode.IsEfficient, codeword length N, list bound L, p-soundness and selective p-correction at every supported length; reason: the components of Definition 3.15 in the published SeededCode notions
--   - encoding: crs = (λ, k, N, P̃_Enc, P̃_Dec); 'padding unused random bits'; lists in lexicographic order → a tuple of strings read back by choice of the unique preimage; each GenProg reads the first progCoins bits of its tape; padded decoder output of L + 1 flagged slots; reason: fixed representations of the paper's objects
--   - encoding: a sufficiently large polynomial k_min with (6.2) for every polynomially bounded k ≥ k_min → PolyBounded k_min and the length requirements and (6.2) at every k_min(λ) ≤ k ≤ 2^λ; reason: the supported range of p.38
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 6.4, p.41 (PDF p.44); Construction 6.1, pp.37–40; Lemma 6.2, p.40

import Mathlib
import Definitions.Def_SeededShannon_Supplement_Constr61

set_option autoImplicit false

namespace SeededShannon.Supplement

open NoisyOWMPC SeededShannon

/-- **Theorem 6.4 (Selective computational correctness)** (Dujmovic, Lu, Silbak, Wichs, *Shannon Rate
Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript sha256
52f4b606…a769709), Theorem 6.4, p.41): assume the primitives in Construction 6.1 satisfy their
stated definitions. Then Construction 6.1 is a selectively `(p, L)`-correct seeded code in the sense
of Definition 3.15, with the list bound `L = t · L_pprc(λ, ℓhash) · L_bal(N)` of Lemma 6.2: for every
efficient adversary `A = (A₁, A₂)`, `ExpCorrect^{(p)}(A, λ)` outputs `1` with negligible
probability. Its decoder is also `p`-sound.

**Formalization Note** "The primitives satisfy their stated definitions" is `Constr61.Valid`.
Setup obfuscates circuits for `EncodeProg` and `DecodeProg` "padded to common polynomial size"
(p.38): the statement holds for every polynomial-time circuit builder that computes the two programs
exactly at padded sizes at least thresholds `S₀_E`, `S₀_D` (polynomials, which exist), the
decoder's padded output having room for `L + 1` candidates. The conclusion consists of the parts of
a "seeded code in the sense of Definition 3.15" (three efficient algorithms: the published
`SeededCode.IsEfficient`), the codeword length `N(λ, k)`, the list bound `L`, `p`-soundness and
selective `p`-correction, at every supported length `k_min(λ) ≤ k ≤ 2^λ`. -/
theorem theorem_6_4 (X : Constr61) (hX : X.Valid) :
    ∃ S0E S0D : ℕ → ℕ → ℕ, PolyBounded₂ S0E ∧ PolyBounded₂ S0D ∧
      ∀ B : Builders61 X, B.Valid S0E S0D →
        B.code61.IsEfficient X.supp ∧
        B.code61.EncodeLength X.supp ∧ B.code61.ListBound X.supp X.Llist ∧
        B.code61.Sound X.supp X.p ∧ B.code61.SelectivelyCorrect X.supp X.p := by sorry

end SeededShannon.Supplement
