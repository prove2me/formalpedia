-- Prove2me | Theorems.Thm_ProofCryptoSynergy_claim_42
-- name    : ProofCryptoSynergy.claim_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:06.680207+00:00
-- url     : https://prove2.me/theorems/81ee6c5f-9c5c-4afa-9eae-407318b2dd56
-- title:
--   Claim 42 (Conditional Security; corrected: NIWI run at $\max(\lambda,|\varphi\vee\psi_\lambda|)$) — a simulator makes $(\mathrm{Gen}',\mathrm{Eval}')$ secure
-- statement:
--   Let $(\mathrm{Gen},\mathrm{Eval})$ be a subexponentially secure keyed OWP, $(P_{\mathrm{NIWI}},V_{\mathrm{NIWI}})$ a NIWI, $(f,g)$ a witness-preserving reduction of $L$ to SAT, $p^*$ a polynomial and $\varepsilon^*(\lambda)=2^{-\lambda^{\Omega(1)}}$. There is $\delta_1>0$ such that for every $\delta'\in(0,\delta_1]$ and $c\ge1$, for all sufficiently large $\eta$ and every $\Psi$: with $\lambda=\eta^c$, if $\Pi=\Pi[\Psi]$ admits a $p^*(\lambda)$-size, $\varepsilon^*(\lambda)$-indistinguishable simulator on $\lambda$, then for every circuit $C$ of size at most $2^{\eta^{\delta'}}$,
--   $$\Pr[C((k,\pi),\mathrm{Eval}'_{\Pi,c}(1^\eta,(k,\pi),x))=x]\le 2^{-\eta^{\delta'}},$$
--   over $(k,\pi)\leftarrow\mathrm{Gen}'_{\Pi,c}(1^\eta)$ and $x\leftarrow\{0,1\}^{d(\eta)}$.
--
--   Security of the extended permutation is a $\Pi_1$ property of $\Psi$; this claim shows it holds at every satisfiable $\psi_\lambda$, which is what Claim 43 feeds to Lemma 33.
--
--   Differences from the source:
--   - correction: P[Ψ], V[Ψ] run the NIWI at 1^λ → the NIWI runs at 1^{max(λ, |φ ∨ ψ_λ|)} (secParam); reason: printed, Lemma 32 item 2 is false: Definition 14 only covers |φ ∨ ψ_λ| ≤ λ, and a NIWI whose verifier also accepts every φ with |φ| > λ satisfies Definition 14 yet accepts all proofs for unsatisfiable φ, ψ_λ of size λ. The raised parameter is polynomial and only strengthens the indistinguishability used
--   - reading: δ′ fixed by (a)–(c), threshold on η unspecified → ∃ δ₁ > 0, ∀ δ′ ∈ (0, δ₁], ∀ c ≥ 1, ∀ᶠ η, ∀ Ψ; reason: any δ′ meeting (a), (b) serves; Claim 43 applies the claim to every satisfiable ψ, so the threshold must not depend on Ψ
--   - generalization: p*, ε* as in Lemma 32 → p* any polynomial and ε* any positive function with ε*(λ) ≤ 2^{−λ^δ} eventually; reason: Lemma 32's p*, ε* have these properties, so the Lean statement specializes to the printed one; the proof uses only these properties
--   - reading: "Let c ∈ N be arbitrary" → c ≥ 1; reason: at c = 0, λ = 1 for all η and the printed inequality 2^{1+η^δ} < 1/ε*(η^c) fails
--   - encoding: Π[Ψ] of Definition 31 used "for L" → an arbitrary polynomial-time witness-preserving reduction (f, g) of L to SAT; reason: Definition 31 is for SAT; a reduction exists by Cook–Levin and the statement holds for each one
--   - reading: ε(λ) = 2^{−λ^{Ω(1)}} and "for all λ" in Definition 14 → ∃ δ > 0, for all large λ, security 2^{−λ^δ}; reason: Ω(1) is asymptotic; at finitely many small λ the function ε may be at least 1, where ≈_ε says nothing
--   - reading: Definition 18 does not bound d(η) → d polynomially bounded; reason: p.14 has x ∈ {0,1}^{poly(η)} and the proof of Proposition 20 says n = poly(η)
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: boolean circuits A on a distribution over {0,1}*; Pr over the distribution → circuits with any number of inputs reading padIn of the string; probabilities as averages over coins; reason: a circuit has a fixed number of inputs; no instance changes
--   - encoding: randomized algorithms with poly coins → a coin count bounded by a polynomial and a deterministic function of the coin string; reason: a randomized algorithm is a deterministic one with its coins as input
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Claim 42, p.35 (PDF 37)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_HasSimulator
import Definitions.Def_ProofCryptoSynergy_primeInvProb

open LaconicBarrier

namespace ProofCryptoSynergy

/-- **Claim 42** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.35 (PDF 37); setting of the proof of Theorem 39, pp.34–35). Let `c` be arbitrary. For all sufficiently large `η`, with
`λ = η^c`: if `Π[Ψ]` admits a `p*(λ)`-size, `ε*(λ)`-indistinguishable simulator on `λ`, then for every circuit `C` of size at most `2^{η^{δ′}}`,
`Pr[C((k, π), Eval′_{Π,c}(1^η, (k, π), x)) = x] ≤ 2^{-η^{δ′}}` (eq. (2)).

**Formalization Note**
1. `δ′` is any sufficiently small positive constant (the paper fixes one by conditions (a)–(c)), and the threshold on `η` does not depend on `Ψ`, because the
   proof of Claim 43 applies the claim to every satisfiable `ψ`.
2. `p*` is any polynomial and `ε*` any positive function with `ε*(λ) = 2^{-λ^{Ω(1)}}`, which is all that "as in Lemma 32" uses.
3. `c ≥ 1`: at `c = 0` one has `λ = 1` for all `η` and the printed inequality `2^{1+η^{δ}} < 1/ε*(η^c)` fails.
4. `Π` is for `L` through an explicit witness-preserving reduction `(f, g)`; `P[Ψ]`, `V[Ψ]` as corrected in `secParam`. -/
theorem claim_42 (W : KeyedOWP) (hW : IsSubexpKeyedOWP W) (N : NIWIScheme) (c₀ : ℕ)
    (hN : IsSubexpNIWI N (fun n => (n + 2) ^ c₀)) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) (hfg : IsWitnessReduction W f g)
    (εs : ℕ → ℝ) (ps : Polynomial ℕ) (hpos : ∀ lam, 0 < εs lam)
    (hsmall : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ lam : ℕ in Filter.atTop, εs lam ≤ (2 : ℝ) ^ (-((lam : ℝ) ^ δ))) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ' : ℝ, 0 < δ' → δ' ≤ δ₁ → ∀ c : ℕ, 1 ≤ c →
      ∀ᶠ η : ℕ in Filter.atTop, ∀ Ψ : ℕ → List Bool, (∀ lam, (Ψ lam).length ≤ lam) →
        HasSimulator (psiProver N Ψ) (η ^ c) (ps.eval (η ^ c)) (εs (η ^ c)) →
        ∀ (m : ℕ) (C : MCircuit m), (C.size : ℝ) ≤ (2 : ℝ) ^ ((η : ℝ) ^ δ') →
          primeInvProb W N Ψ f g c η C ≤ (2 : ℝ) ^ (-((η : ℝ) ^ δ')) := by sorry

end ProofCryptoSynergy
