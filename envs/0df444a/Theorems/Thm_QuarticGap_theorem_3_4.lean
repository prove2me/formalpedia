-- Prove2me | Theorems.Thm_QuarticGap_theorem_3_4
-- name    : QuarticGap.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:23.948231+00:00
-- url     : https://prove2.me/theorems/4acfad8d-1af3-4b92-8b0d-687c84adea30
-- title:
--   Theorem 3.4 (transfer theorem) — $|\Lambda_F| \le \eta+\tau+2\varepsilon+(2+\Phi_{\max})\delta_{\mathcal G}$
-- statement:
--   Let $S$ be a set of $K$ characters, $Y \supseteq S$ a finite outcome set with $Y \setminus S \ne \emptyset$, $\mathcal G$ a set of Boolean functions with $\delta_{\mathcal G} = P(f \notin \mathcal G)$, and for each $f \in \mathcal G$ let $x(f) \in \mathbb C^Y$ be a nonzero target. Let $F$ be the sine or the cosine test, and suppose $\gamma \in \mathbb C^S$, $\beta \in \mathbb C$, $d > 0$, $\eta \ge 0$, independent of $f$, satisfy
--   $$
--   \mathbb E\Bigl[\mathbf 1[f\in\mathcal G]\Bigl|\sum_{j\in Y} p_{x(f)}(j)F(f,j)-\Phi(f)\Bigr|\Bigr] \le \eta .
--   $$
--   Let $q, \tau \ge 0$ be such that every classical algorithm making at most $q$ queries on every input and every run satisfies $|\mathbb E F(f,J_A)| \le \tau$. Let $\varepsilon \ge 0$. If a classical algorithm makes at most $q$ queries on every input in $\mathcal G$ and every run, and its output law is within total variation distance $\varepsilon$ of $p_{x(f)}$ for every $f \in \mathcal G$, then
--   $$
--   |\Lambda_F| \le \eta+\tau+2\varepsilon+(2+\Phi_{\max})\delta_{\mathcal G} .
--   $$
--
--   It reduces a sampling lower bound for any target close to an affine function of the Fourier coefficients to the two conditions on $x(f)$.
--
--   **Formalization Note** The hypothesis on $(q,\tau)$ is over all inputs, whereas the algorithm is bounded on $\mathcal G$ only.
--
--   Differences from the source:
--   - encoding: a set of K characters → a nonempty Finset S with K = S.card; reason: the source divides by K and takes log(2K); K = 0 is meaningless
--   - encoding: Y ⊇ S → an embedding e of S into Y; Y ∖ S ≠ ∅ is that e is not surjective; reason: the source itself identifies S with coordinates of the outcome set
--   - reading: a randomized classical algorithm → QueryAlg, a behaviour strategy on transcripts with unrestricted computation; reason: an algorithm with private coins has perfect recall, so Kuhn gives the same law; the input reaches it only through the answers
--   - encoding: output distribution within total variation distance ε → sampleErr, which counts the mass of non-halting runs as an extra outcome; reason: it is TV for an algorithm that halts almost surely, and gives a non-halting algorithm no advantage
--   - encoding: q ≥ 0 → q a natural number; reason: a query count is an integer, and at most q queries is at most ⌊q⌋ queries
--   - encoding: independent uniform signs, uniformly random f or W → the uniform distribution on the finite set of sign functions; reason: the same law
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Theorem 3.4, p.25

import Mathlib
import Definitions.Def_QuarticGap_Phi

open QAlgorithms

namespace QuarticGap

/-- Theorem 3.4, the transfer theorem (arXiv:2610.42069 (file sha256 9f68aaf9…), p.25). If (13) holds
with `γ, β, d, η` independent of `f`, if every algorithm making at most `q` queries on every input
and every run satisfies `|𝔼F(f, J_A)| ≤ τ`, and if an algorithm makes at most `q` queries on every
input in `G` and every run and has output law within `ε` of `p_{x(f)}` for every `f ∈ G`, then
`|Λ_F| ≤ η + τ + 2ε + (2 + Φ_max)δ_G`.

**Formalization Note** The hypothesis on `(q, τ)` is over all inputs, while the algorithm is bounded
on `G` only. `Y ⊇ S` is the embedding `e`, and `Y ∖ S ≠ ∅` is that `e` is not surjective. A real `q`
is the same as its floor, so `q : ℕ`. -/
theorem theorem_3_4 {m : ℕ} (hm : 2 ≤ m) (S : Finset (Qubits m)) (hS : S.Nonempty) {Y : Type*} [Fintype Y] (e : S ↪ Y)
    (hY : ¬ Function.Surjective e) (G : Set (Qubits m → ℤˣ)) (x : (Qubits m → ℤˣ) → Y → ℂ)
    (hx : ∀ f ∈ G, x f ≠ 0) (k : TestKind) (γ : S → ℂ) (β : ℂ) (d η : ℝ) (hd : 0 < d) (hη : 0 ≤ η)
    (h13 : transferGap k e G x γ β d ≤ η)
    (q : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hqτ : ∀ A : QueryAlg (Qubits m) ℤˣ Y, (∀ f, A.MakesAtMost (directRespond f) q) →
      |expF k e A| ≤ τ)
    (ε : ℝ) (hε : 0 ≤ ε) (A : QueryAlg (Qubits m) ℤˣ Y)
    (hAq : ∀ f ∈ G, A.MakesAtMost (directRespond f) q)
    (hAε : ∀ f ∈ G, A.sampleErr (directRespond f) (lenSqDist (x f)) ≤ ε) :
    |Lambda k S γ β d| ≤
      η + τ + 2 * ε + (2 + PhiMax S γ β d) * uProb (fun f : Qubits m → ℤˣ => f ∉ G) := by sorry

end QuarticGap
