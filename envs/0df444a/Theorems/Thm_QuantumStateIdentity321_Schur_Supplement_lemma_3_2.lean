-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_lemma_3_2
-- name    : QuantumStateIdentity321.Schur.Supplement.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:53:28.793243+00:00
-- url     : https://prove2.me/theorems/2d32aa61-3f08-4985-b19c-937925ea8e58
-- title:
--   Lemma 3.2 — the $k$-fold swap test separates fidelity $\ge1-\varepsilon$ from fidelity $\le(1+\sqrt\varepsilon)/2$ with error $e^{-k\gamma^2/8}$
-- statement:
--   Let $\varepsilon\in(0,1/4)$, $\gamma=\frac12-\sqrt\varepsilon$, $k\ge1$, and let $|\psi\rangle,|\varphi\rangle\in\mathbb C^d$ be unit vectors. Consider the $k$-fold swap test (Algorithm 1) with threshold $\tau=(7-2\varepsilon+\sqrt\varepsilon)/8$, run on $k$ copies of $|\psi\rangle$ and $k$ copies of $|\varphi\rangle$. It is a two-outcome measurement, and
--
--   1. if $|\langle\psi|\varphi\rangle|^2\ge1-\varepsilon$, it accepts with probability at least $1-e^{-k\gamma^2/8}$;
--   2. if $|\langle\psi|\varphi\rangle|^2\le\frac{1+\sqrt\varepsilon}2$, it rejects with probability at least $1-e^{-k\gamma^2/8}$.
--
--   In particular, as a tester on two input states, it solves $\mathrm{QSI}^\varepsilon_2$ with error at most $e^{-k\gamma^2/8}$:
--
--   $$
--   \Pr[\text{reject}\mid\text{yes}]\le e^{-k\gamma^2/8},\qquad \Pr[\text{accept}\mid\text{no}]\le e^{-k\gamma^2/8}.
--   $$
--
--   This is the pairwise test that Algorithm 2 runs on every edge of its random matchings; the no-side threshold $(1+\sqrt\varepsilon)/2$ is the one guaranteed for witness edges by Lemma 3.1.
--
--   **Formalization Note** "Rejects with probability at least $1-e$" is stated as "accepts with probability at most $e$", the two outcomes having probabilities summing to $1$.
--
--   Differences from the source:
--   - encoding: the k-fold swap test with destructive (Bell-basis) swap tests → the accept effect Σ_{x : p̂(x) ≥ τ} ⊗ₛ Π_{xₛ} with Π = ½(I ± SWAP); reason: the source states (p.10) that its circuit reproduces exactly this outcome law and uses only it
--   - encoding: k-fold swap test (p̂ = (1/k)Σ X⁽ˢ⁾) → hypothesis 1 ≤ k; reason: the average p̂ is undefined at k = 0; no instance of the source is excluded
--   - encoding: rejects with probability ≥ 1 − e → accepts with probability ≤ e; reason: the two outcome probabilities sum to 1 on unit inputs; same instances
--   - generalization: local dimension d ≥ 2 (Definition 1.1's standing assumption) → every d; reason: the swap-test analysis holds in every dimension (for d = 0 there are no unit vectors); it specializes to every d ≥ 2
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Lemma 3.2, PDF/printed p.10, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SwapMatching

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Lemma 3.2, p.10: for `ε ∈ (0, 1/4)`, `γ = 1/2 − √ε` and every `k ≥ 1`, the `k`-fold swap test
(Algorithm 1) with threshold `τ = (7 − 2ε + √ε)/8`, run on `k` copies of `|ψ⟩` and `k` copies of
`|φ⟩`, is a two-outcome measurement that accepts with probability at least `1 − e^{−kγ²/8}` when
`|⟨ψ|φ⟩|² ≥ 1 − ε` and rejects with probability at least `1 − e^{−kγ²/8}` (accepts with
probability at most `e^{−kγ²/8}`) when `|⟨ψ|φ⟩|² ≤ (1 + √ε)/2`; in particular it solves
`QSI^ε_2` with error at most `e^{−kγ²/8}`. -/
theorem lemma_3_2 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4) (k : ℕ) (hk : 1 ≤ k) (d : ℕ) :
    ∃ T : Tester 2 k d, T.effect = kFoldEffect k d (swapThreshold ε) ∧
      (∀ ψ φ : State d, ‖ψ‖ = 1 → ‖φ‖ = 1 →
        (1 - ε ≤ fidelity ψ φ →
          1 - Real.exp (-((k : ℝ) * (1 / 2 - Real.sqrt ε) ^ 2 / 8)) ≤ acceptProb T ![ψ, φ]) ∧
        (fidelity ψ φ ≤ (1 + Real.sqrt ε) / 2 →
          acceptProb T ![ψ, φ] ≤ Real.exp (-((k : ℝ) * (1 / 2 - Real.sqrt ε) ^ 2 / 8)))) ∧
      SolvesQSI T ε (Real.exp (-((k : ℝ) * (1 / 2 - Real.sqrt ε) ^ 2 / 8))) := by sorry

end QuantumStateIdentity321.Schur.Supplement
