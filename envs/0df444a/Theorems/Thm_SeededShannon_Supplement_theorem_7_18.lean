-- Prove2me | Theorems.Thm_SeededShannon_Supplement_theorem_7_18
-- name    : SeededShannon.Supplement.theorem_7_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:47:49.542563+00:00
-- url     : https://prove2.me/theorems/c0f5d250-8cce-464c-92d1-ca3dafb6acb1
-- title:
--   Theorem 7.18 — selective-to-adaptive transformation in the random-oracle model
-- statement:
--   For every supported polynomially bounded message length, Construction 7.17 converts selective $(p,L)$-correctness (Definition 3.15) into adaptive $(p,L)$-correctness (Definition 7.16) in the random-oracle model, with the same error radius and no increase in list size. A uniquely decodable base code gives a uniquely decodable transformed code. If the base rate on $d$-bit messages is at least $R$, the transformed rate is at least
--   $$\frac{Rk}{k+\ell_{\mathrm{tag}}}.$$
--   The base code may itself use a random oracle independent of $H$ and $P$.
--
--   Composed with Theorems 6.4 and 7.15 this gives adaptively correct seeded codes at rate $1-H(p)-\varepsilon$ in the random-oracle model.
--
--   **Formalization Note** The model has a random oracle $H$, an ideal permutation $(P,P^{-1})$ of $\{0,1\}^{k+\lambda}$ and the base code's own random oracle, independent and uniform, with $\ell_{\mathrm{tag}}=\lambda$.
--
--   Differences from the source:
--   - reading: in the random-oracle model, with P implemented from the random oracle by an indifferentiable construction → a model with a random oracle H, an ideal permutation (P, P⁻¹) and the base code's random oracle, independent and uniform; reason: the proof's first sentence: 'By the composition argument above, we may take P to be an ideal permutation'
--   - generalization: the base code is selectively (p, L)-correct in the random-oracle model (first stage with oracle access) → selective correctness against first stages that fix the message without oracle queries; reason: a weaker hypothesis: a code correct against oracle-querying first stages is correct against these; the reduction of the proof makes no first-stage query
--   - encoding: the base code's random oracle → a uniformly random function {0,1}^{oIn(λ,d)} → {0,1}^{oOut(λ,d)} at each (λ, d); reason: a random oracle restricted to the input length the code queries
--   - encoding: uniquely decodable base / transformed code → list bound 1 and failure Decode(y) ≠ [x*]; reason: Definitions 3.15 and 7.16 identify a unique output with a list of size at most one
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 7.18, p.54 (PDF p.57); Construction 7.17 and Definition 7.16, p.54; proof, p.55

import Mathlib
import Definitions.Def_SeededShannon_Supplement_OSeededCode

set_option autoImplicit false

namespace SeededShannon.Supplement

open NoisyOWMPC SeededShannon

/-- **Theorem 7.18 (Selective-to-adaptive transformation)** (Dujmovic, Lu, Silbak, Wichs, *Shannon
Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript sha256
52f4b606…a769709), Theorem 7.18, p.54): for every supported polynomially bounded message length,
Construction 7.17 converts selective `(p, L)`-correctness (Definition 3.15) into adaptive
`(p, L)`-correctness (Definition 7.16) in the random-oracle model, with the same error radius and no
increase in list size. A uniquely decodable base code gives a uniquely decodable transformed code.
If the base rate on `d`-bit messages is at least `R`, the transformed rate is at least
`Rk/(k + ℓtag)`. The base code may itself use a random oracle independent of `H` and `P`.

**Formalization Note** The model has a random oracle `H : {0,1}^k → {0,1}^{ℓtag}` (`ℓtag = λ`), an
ideal permutation `(P, P^{−1})` of `{0,1}^{k+ℓtag}` and the base code's own random oracle, all
independent and uniform (the proof's first sentence: "By the composition argument above, we may take
`P` to be an ideal permutation"; the indifferentiable instantiation of `P` from the random oracle is
not formalized). The transformed code at message length `k` uses the base code at `d = k + λ`; its
codeword length is the base's `N(λ, k + λ)`. The selective hypothesis is against first stages that
make no oracle query (`OSeededCode.SelectivelyCorrect`). Unique decodability is list size `1`. -/
theorem theorem_7_18 (C : OSeededCode) (supp : ℕ → ℕ → Prop) (p : ℝ) (L : ℕ → ℕ → ℕ) :
    (C.ListBound supp L → C.SelectivelyCorrect supp p →
      Adaptive717 C supp p false ∧ ListBound717 C supp L) ∧
    (C.ListBound supp (fun _ _ => 1) → C.SelectivelyCorrectUnique supp p →
      Adaptive717 C supp p true ∧ ListBound717 C supp (fun _ _ => 1)) ∧
    ∀ (R : ℝ) (lam k : ℕ), supp lam (k + lam) →
      R ≤ ((k + lam : ℕ) : ℝ) / C.N lam (k + lam) →
      R * k / (k + lam) ≤ (k : ℝ) / C.N lam (k + lam) := by sorry

end SeededShannon.Supplement
