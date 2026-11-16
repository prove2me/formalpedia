-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_lemma_4_2
-- name    : QuantumStateIdentity321.Schur.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:57:36.012211+00:00
-- url     : https://prove2.me/theorems/b7fa955b-9573-4803-9042-9086bda759ff
-- title:
--   Lemma 4.2 — the fidelity-sum estimator $Z_i=\mathrm{ct}_S(i)+\mathrm{ct}_{S'}(n+1-i)$: mean $\sum_{j\ne i}F_{ij}$, range $[-(n-1),n-1]$
-- statement:
--   Let $n\ge2$, $d\ge2$, let $|\psi_1\rangle,\dots,|\psi_n\rangle\in\mathbb C^d$ be unit vectors and $F_{ij}=|\langle\psi_i|\psi_j\rangle|^2$, and fix $i\in[n]$. Measure $\{M_{\lambda,S}\}$ (Corollary 4.1) on the forward block $|\psi_1\rangle\otimes\cdots\otimes|\psi_n\rangle$, with outcome $(\lambda,S)$, and independently on the reverse block $|\psi_n\rangle\otimes\cdots\otimes|\psi_1\rangle$, with outcome $(\lambda',S')$, and set
--
--   $$
--   Z_i=\mathrm{ct}_S(i)+\mathrm{ct}_{S'}(n+1-i).
--   $$
--
--   The Born probabilities of the outcome pairs form a probability distribution, and
--
--   $$
--   \mathbb E[Z_i]=\sum_{j\ne i}F_{ij},\qquad -(n-1)\le Z_i\le n-1 .
--   $$
--
--   Algorithm 3 averages independent copies of these bounded estimators and compares $\min_i\bar Z_i$ with a threshold.
--
--   **Formalization Note** The random variable of the source is the concrete statistic above under the product Born law $p(S)\,p'(S')$ with $p(S)=\langle\Psi|M_{\lambda,S}|\Psi\rangle$; the range bound holds for every outcome pair. The source's $n+1-i$ is `Fin.rev i`.
--
--   Differences from the source:
--   - encoding: "there exists a random variable Z_i obtained from two joint spectral measurements" → the concrete statistic ct_S(i) + ct_{S′}(n+1−i) under the product Born law of the two measurements, with the law's normalization as a conjunct; reason: this is the random variable of the source's proof; same instances
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Lemma 4.2, PDF/printed p.15, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SchurSampling

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma 4.2 (fidelity-sum estimator), pp.15–16: for unit vectors `|ψ₁⟩, …, |ψₙ⟩` (`n ≥ 2`,
`d ≥ 2`) and `i ∈ [n]`, measure `{M_{λ,S}}` on the forward block `|ψ₁⟩ ⊗ ⋯ ⊗ |ψₙ⟩` (outcome
`(λ, S)`) and independently on the reverse block `|ψₙ⟩ ⊗ ⋯ ⊗ |ψ₁⟩` (outcome `(λ', S')`), and set
`Z_i = ct_S(i) + ct_{S'}(n + 1 − i)`. The Born weights form a probability distribution,
`E[Z_i] = Σ_{j ≠ i} F_ij` with `F_ij = |⟨ψ_i|ψ_j⟩|²`, and `−(n − 1) ≤ Z_i ≤ n − 1`. -/
theorem lemma_4_2 (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (ψ : Fin n → State d)
    (hψ : ∀ j, ‖ψ j‖ = 1) (i : Fin n) :
    (∀ o : SchurOutcome n d × SchurOutcome n d,
        0 ≤ bornProb (schurProj (d := d) o.1.val) (forwardInput ψ) *
          bornProb (schurProj (d := d) o.2.val) (reverseInput ψ)) ∧
      (∑ o : SchurOutcome n d × SchurOutcome n d,
        bornProb (schurProj (d := d) o.1.val) (forwardInput ψ) *
          bornProb (schurProj (d := d) o.2.val) (reverseInput ψ)) = 1 ∧
      (∑ o : SchurOutcome n d × SchurOutcome n d,
        bornProb (schurProj (d := d) o.1.val) (forwardInput ψ) *
          bornProb (schurProj (d := d) o.2.val) (reverseInput ψ) *
          ((content o.1.val i : ℝ) + (content o.2.val (Fin.rev i) : ℝ))) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i), fidelity (ψ i) (ψ j) ∧
      ∀ o : SchurOutcome n d × SchurOutcome n d,
        -((n : ℝ) - 1) ≤ (content o.1.val i : ℝ) + (content o.2.val (Fin.rev i) : ℝ) ∧
        (content o.1.val i : ℝ) + (content o.2.val (Fin.rev i) : ℝ) ≤ (n : ℝ) - 1 := by sorry

end QuantumStateIdentity321.Schur.Supplement
