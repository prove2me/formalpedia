-- Prove2me | Theorems.Thm_ProofCryptoSynergy_claim_43
-- name    : ProofCryptoSynergy.claim_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:33.0842+00:00
-- url     : https://prove2.me/theorems/5e9dae5a-9574-4589-81f0-0da522541f38
-- title:
--   Claim 43 (Security of the Final Construction; corrected: NIWI run at $\max(\lambda,|\varphi\vee\psi_\lambda|)$)
-- statement:
--   Assume a subexponentially secure keyed OWP and a NIWI exist and there is no infinitely-often subexponentially optimal proof system, and let $(f,g)$ be a witness-preserving reduction of $L$ to SAT. Then there are constants $c^*$ and $\delta>0$ and a P-uniform family of unsatisfiable formulas $\Psi^*=\{\psi^*_\lambda\}$ such that with $\Pi^*=\Pi[\Psi^*]$, for all large $\eta$ and every circuit $C$ of size at most $2^{\eta^\delta}$,
--   $$\Pr_{(k,\pi)\leftarrow\mathrm{Gen}'_{\Pi^*,c^*}(1^\eta),\,x\leftarrow\{0,1\}^{d(\eta)}}[C((k,\pi),\mathrm{Eval}'_{\Pi^*,c^*}(1^\eta,(k,\pi),x))=x]\le 2^{-\eta^\delta}.$$
--
--   So one sound proof system makes the certified permutation secure; together with completeness and soundness this gives Theorem 39.
--
--   Differences from the source:
--   - correction: P[Ψ], V[Ψ] run the NIWI at 1^λ → the NIWI runs at 1^{max(λ, |φ ∨ ψ_λ|)} (secParam); reason: printed, Lemma 32 item 2 is false: Definition 14 only covers |φ ∨ ψ_λ| ≤ λ, and a NIWI whose verifier also accepts every φ with |φ| > λ satisfies Definition 14 yet accepts all proofs for unsatisfiable φ, ψ_λ of size λ. The raised parameter is polynomial and only strengthens the indistinguishability used
--   - reading: "for every circuit C of size at most 2^{η^δ}" with no quantifier on η → for all large η; reason: η is unbound in the printed claim; Definition 18, item 4 has "for sufficiently large η" and the printed proof concludes "If η is sufficiently large". Read as every η the claim is false: if d(1) = 0, the circuit with no outputs inverts with probability 1 > 2^{−1}
--   - encoding: Π[Ψ] of Definition 31 used "for L" → an arbitrary polynomial-time witness-preserving reduction (f, g) of L to SAT; reason: Definition 31 is for SAT; a reduction exists by Cook–Levin and the statement holds for each one
--   - reading: ε(λ) = 2^{−λ^{Ω(1)}} and "for all λ" in Definition 14 → ∃ δ > 0, for all large λ, security 2^{−λ^δ}; reason: Ω(1) is asymptotic; at finitely many small λ the function ε may be at least 1, where ≈_ε says nothing
--   - reading: Definition 18 does not bound d(η) → d polynomially bounded; reason: p.14 has x ∈ {0,1}^{poly(η)} and the proof of Proposition 20 says n = poly(η)
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Claim 43, p.36 (PDF 38)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
import Definitions.Def_ProofCryptoSynergy_primeInvProb

open LaconicBarrier

namespace ProofCryptoSynergy

/-- **Claim 43** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.36 (PDF 38)). Under the assumptions of Theorem 39, there are constants `c*` and `δ > 0` and a P-uniform family of unsatisfiable
formulas `Ψ* = {ψ*_λ}` such that with `Π* = Π[Ψ*]`, for every circuit `C` of size at most `2^{η^δ}`,
`Pr[C((k, π), Eval′_{Π*,c*}(1^η, (k, π), x)) = x] ≤ 2^{-η^δ}`.

**Formalization Note** For all large `η`, as Definition 18, item 4 requires; the printed claim omits this and its proof concludes "If `η` is sufficiently large".
`Π` is for `L` through an explicit witness-preserving reduction `(f, g)`; `P[Ψ]`, `V[Ψ]` as corrected in `secParam`. -/
theorem claim_43 (W : KeyedOWP) (hW : IsSubexpKeyedOWP W) (N : NIWIScheme) (c₀ : ℕ)
    (hN : IsSubexpNIWI N (fun n => (n + 2) ^ c₀)) (hopt : NoIoSubexpOptimalPPS)
    (f : List Bool → List Bool) (g : List Bool → List Bool → List Bool)
    (hfg : IsWitnessReduction W f g) :
    ∃ (cs : ℕ) (δ : ℝ) (Ψ : ℕ → List Bool), 1 ≤ cs ∧ 0 < δ ∧ IsPUniformUnsat Ψ ∧
      ∀ᶠ η : ℕ in Filter.atTop, ∀ (m : ℕ) (C : MCircuit m),
        (C.size : ℝ) ≤ (2 : ℝ) ^ ((η : ℝ) ^ δ) →
        primeInvProb W N Ψ f g cs η C ≤ (2 : ℝ) ^ (-((η : ℝ) ^ δ)) := by sorry

end ProofCryptoSynergy
