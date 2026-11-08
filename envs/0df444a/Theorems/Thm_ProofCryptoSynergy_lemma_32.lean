-- Prove2me | Theorems.Thm_ProofCryptoSynergy_lemma_32
-- name    : ProofCryptoSynergy.lemma_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:05.722419+00:00
-- url     : https://prove2.me/theorems/ba1da1b3-3b30-401f-b8be-da3566101f93
-- title:
--   Lemma 32 (corrected: NIWI run at $\max(\lambda,|\varphi\vee\psi_\lambda|)$) — completeness, soundness and the simulator of $(P[\Psi],V[\Psi])$
-- statement:
--   Let $(P_{\mathrm{NIWI}},V_{\mathrm{NIWI}})$ be a NIWI proof system, and consider sequences $\Psi=\{\psi_\lambda\}$ of formulas of size at most $\lambda$. Then:
--   1. for any $\Psi$, $(P[\Psi],V[\Psi])$ has perfect completeness;
--   2. for all $\lambda$, if $\psi_\lambda$ is unsatisfiable, then $(P[\Psi],V[\Psi])$ has perfect soundness on security parameter $\lambda$;
--   3. there are $\varepsilon^*(\lambda)=2^{-\lambda^{\Omega(1)}}$ and a polynomial $p^*$ such that for all $\lambda$, if $\psi_\lambda$ is satisfiable, then $P[\Psi]$ has a $p^*(\lambda)$-size $\varepsilon^*(\lambda)$-indistinguishable simulator on $\lambda$.
--
--   The point of the construction: unsatisfiable $\psi_\lambda$ gives soundness, and satisfiable $\psi_\lambda$ gives zero knowledge, so a property implied by zero knowledge can be transferred to the sound case.
--
--   Differences from the source:
--   - correction: P[Ψ], V[Ψ] run the NIWI at 1^λ → the NIWI runs at 1^{max(λ, |φ ∨ ψ_λ|)} (secParam); reason: printed, Lemma 32 item 2 is false: Definition 14 only covers |φ ∨ ψ_λ| ≤ λ, and a NIWI whose verifier also accepts every φ with |φ| > λ satisfies Definition 14 yet accepts all proofs for unsatisfiable φ, ψ_λ of size λ. The raised parameter is polynomial and only strengthens the indistinguishability used
--   - reading: ε(λ) = 2^{−λ^{Ω(1)}} and "for all λ" in Definition 14 → ∃ δ > 0, for all large λ, security 2^{−λ^δ}; reason: Ω(1) is asymptotic; at finitely many small λ the function ε may be at least 1, where ≈_ε says nothing
--   - reading: "there exists ε*, p*" stated with Ψ in the context → ε* and p* are chosen before Ψ; reason: Claim 42 and Remark 34 use them for all Ψ, and the proof gives them from the NIWI alone
--   - encoding: "perfect soundness on security parameter λ" (not spelled out) → for unsatisfiable φ with |φ| ≤ λ and all π, V[Ψ](φ, π, 1^λ) = 0; reason: the format of Definition 14
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 32, p.29 (PDF 31)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_provePsi
import Definitions.Def_ProofCryptoSynergy_HasSimulator

namespace ProofCryptoSynergy

/-- **Lemma 32** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.29 (PDF 31)). For a NIWI `(P_NIWI, V_NIWI)` and sequences `Ψ = {ψ_λ}` of formulas of size at most `λ`:
1. `(P[Ψ], V[Ψ])` has perfect completeness;
2. for all `λ`, if `ψ_λ` is unsatisfiable, it has perfect soundness on security parameter `λ`;
3. there are `ε*(λ) = 2^{-λ^{Ω(1)}}` and a polynomial `p*` such that for all `λ`, if `ψ_λ` is satisfiable, `P[Ψ]` has a
   `p*(λ)`-size `ε*(λ)`-indistinguishable simulator on `λ`.

**Formalization Note** `P[Ψ]`, `V[Ψ]` run the NIWI at the security parameter `secParam`, the correction of Definition 31 explained there;
as printed, item 2 is false. `ε*` and `p*` do not depend on `Ψ`: Claim 42 and Remark 34 use them for all `Ψ`. -/
theorem lemma_32 (N : NIWIScheme) (c₀ : ℕ) (hN : IsSubexpNIWI N (fun n => (n + 2) ^ c₀)) :
    (∀ Ψ : ℕ → List Bool, (∀ lam, (Ψ lam).length ≤ lam) → PsiComplete N Ψ) ∧
    (∀ Ψ : ℕ → List Bool, (∀ lam, (Ψ lam).length ≤ lam) →
      ∀ lam, Ψ lam ∉ SAT → PsiSoundAt N Ψ lam) ∧
    ∃ (εs : ℕ → ℝ) (ps : Polynomial ℕ), (∀ lam, 0 < εs lam) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ lam : ℕ in Filter.atTop, εs lam ≤ (2 : ℝ) ^ (-((lam : ℝ) ^ δ))) ∧
      ∀ Ψ : ℕ → List Bool, (∀ lam, (Ψ lam).length ≤ lam) → ∀ lam, Ψ lam ∈ SAT →
        HasSimulator (psiProver N Ψ) lam (ps.eval lam) (εs lam) := by sorry

end ProofCryptoSynergy
