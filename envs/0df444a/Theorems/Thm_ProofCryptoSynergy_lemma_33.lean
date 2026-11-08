-- Prove2me | Theorems.Thm_ProofCryptoSynergy_lemma_33
-- name    : ProofCryptoSynergy.lemma_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:57.698919+00:00
-- url     : https://prove2.me/theorems/131c211b-19a6-4660-874e-ae4099aec931
-- title:
--   Lemma 33 (P-uniform alternative; corrected: NIWI run at $\max(\lambda,|\varphi\vee\psi_\lambda|)$) — $R_{c^*}$ holds on a sound $\Psi^*$
-- statement:
--   Assume a NIWI proof system exists and there is no infinitely-often subexponentially optimal proof system. Let $R_c(\psi)=\forall w\,P_c(\psi,w)$, $c\ge1$, with $|w|\le 2^{|\psi|^{1/c}}$ and $P_c(\psi,w)$ computable in time $2^{O(|\psi|^{1/c})}$, such that for every $c$, $R_c(\psi)$ is true for all large enough $\psi\in\mathrm{SAT}$. Then there are a P-uniform family of unsatisfiable formulas $\Psi^*=\{\psi^*_\lambda\}$ and a constant $c^*\ge1$ such that for all large $\lambda$, $R_{c^*}(\psi^*_\lambda)$ is true, and $(P[\Psi^*],V[\Psi^*])$ is uniformly efficiently computable with perfect completeness and soundness.
--
--   This is the transfer principle of the paper's proof framework: a consequence of an imagined simulator holds outright in a sound proof system.
--
--   Differences from the source:
--   - correction: P[Ψ], V[Ψ] run the NIWI at 1^λ → the NIWI runs at 1^{max(λ, |φ ∨ ψ_λ|)} (secParam); reason: printed, Lemma 32 item 2 is false: Definition 14 only covers |φ ∨ ψ_λ| ≤ λ, and a NIWI whose verifier also accepts every φ with |φ| > λ satisfies Definition 14 yet accepts all proofs for unsatisfiable φ, ψ_λ of size λ. The raised parameter is polynomial and only strengthens the indistinguishability used
--   - reading: an arbitrary family of formulas R_c, indexed by c ≥ 1 → one machine computing P_c(ψ, w) from (1^c, ψ, w); time 2^{a_c |ψ|^{1/c}} with a_c depending on c; reason: the printed proof needs one polynomial-time PPS L_R checking transcripts of P_c for c given in the proof (p.26)
--   - reading: ε(λ) = 2^{−λ^{Ω(1)}} and "for all λ" in Definition 14 → ∃ δ > 0, for all large λ, security 2^{−λ^δ}; reason: Ω(1) is asymptotic; at finitely many small λ the function ε may be at least 1, where ≈_ε says nothing
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
--   - encoding: P_c(ψ, w) computable in time 2^{O(|ψ|^{1/c})} for all ψ → the time bound is required for nonempty ψ only; reason: at |ψ| = 0 the bound 2^{a_c·0} = 1 step cannot even read the input; only the empty formula is excluded, and R_c on one fixed length plays no role in an eventual hypothesis or conclusion
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 33, p.30 (PDF 32)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_PiFamily
import Definitions.Def_ProofCryptoSynergy_provePsi

namespace ProofCryptoSynergy

/-- **Lemma 33, P-uniform alternative** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.30 (PDF 32)). Assume a NIWI exists and no infinitely-often subexponentially optimal
proof system exists. For every family `R_c(ψ) = ∀w P_c(ψ, w)` with `R_c(ψ)` true for all large enough `ψ ∈ SAT`, there are a P-uniform
family of unsatisfiable `Ψ* = {ψ*_λ}` and `c* ≥ 1` such that `R_{c*}(ψ*_λ)` is true for all large `λ`, and `(P[Ψ*], V[Ψ*])` is uniformly
efficiently computable and has perfect completeness and soundness.

**Formalization Note** "All large enough `ψ`" is, for each `c ≥ 1`, some threshold `n₀` on `|ψ|`, as printed; nothing is assumed about how
`n₀` depends on `c`. `P[Ψ]`, `V[Ψ]` as corrected in `secParam`; with `1^λ` and `|ψ*_λ| = λ` the soundness clause would be false. -/
theorem lemma_33 (N : NIWIScheme) (c₀ : ℕ) (hN : IsSubexpNIWI N (fun n => (n + 2) ^ c₀))
    (hopt : NoIoSubexpOptimalPPS) (F : PiFamily) (hF : F.TimeBounded)
    (hR : ∀ c : ℕ, 1 ≤ c → ∃ n₀ : ℕ, ∀ ψ ∈ SAT, n₀ ≤ ψ.length → F.R c ψ) :
    ∃ (Ψ : ℕ → List Bool) (cs : ℕ), IsPUniformUnsat Ψ ∧ 1 ≤ cs ∧
      (∀ᶠ lam : ℕ in Filter.atTop, F.R cs (Ψ lam)) ∧
      PsiEfficient N Ψ ∧ PsiComplete N Ψ ∧ ∀ lam, PsiSoundAt N Ψ lam := by sorry

end ProofCryptoSynergy
