-- Prove2me | Theorems.Thm_QuarticGap_corollary_3_6
-- name    : QuarticGap.corollary_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:34.956933+00:00
-- url     : https://prove2.me/theorems/bb779d73-c492-40f8-a7ce-4f7165a609d1
-- title:
--   Corollary 3.6 — asymptotic lower bound $cM_\ell/\log(2K_\ell)$ from a sequence of instances of the transfer theorem
-- statement:
--   Consider a sequence of instances of Theorem 3.4, indexed by $\ell$, with $M_\ell \to \infty$ and the same test $F$. Suppose $\Lambda_{F,\ell} \to \Lambda_\infty$, $\eta_\ell \le \eta_\infty$ for all sufficiently large $\ell$, and $(2+\Phi_{\max,\ell})\delta_{\mathcal G,\ell} \to 0$. Let $\varepsilon \ge 0$ be a constant with $2\varepsilon < |\Lambda_\infty|-\eta_\infty$. Then there are $c > 0$ and $\ell_0$ such that, for every $\ell \ge \ell_0$, every classical algorithm that samples within total variation distance $\varepsilon$ on $\mathcal G_\ell$ makes more than
--   $$
--   \frac{cM_\ell}{\log(2K_\ell)}
--   $$
--   queries on some input in $\mathcal G_\ell$, and more than that many queries in expectation on some input in $\mathcal G_\ell$.
--
--   For the linear systems of the mission, $M = n^2$ and $K = n$, which gives the $\Omega(n^2/\log n)$ bound.
--
--   **Formalization Note** $c$ and $\ell_0$ come before the algorithm. An instance is a `TransferInstance`; the numbers $q$, $\tau$ of Theorem 3.4 are not part of it, as the proof takes them from Lemma 3.3.
--
--   Differences from the source:
--   - encoding: a set of K characters → a nonempty Finset S with K = S.card; reason: the source divides by K and takes log(2K); K = 0 is meaningless
--   - encoding: Y ⊇ S → an embedding e of S into Y; Y ∖ S ≠ ∅ is that e is not surjective; reason: the source itself identifies S with coordinates of the outcome set
--   - reading: a randomized classical algorithm → QueryAlg, a behaviour strategy on transcripts with unrestricted computation; reason: an algorithm with private coins has perfect recall, so Kuhn gives the same law; the input reaches it only through the answers
--   - encoding: output distribution within total variation distance ε → sampleErr, which counts the mass of non-halting runs as an extra outcome; reason: it is TV for an algorithm that halts almost surely, and gives a non-halting algorithm no advantage
--   - encoding: independent uniform signs, uniformly random f or W → the uniform distribution on the finite set of sign functions; reason: the same law
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Corollary 3.6, p.26

import Mathlib
import Definitions.Def_QuarticGap_Phi

open QAlgorithms

namespace QuarticGap

/-- Corollary 3.6 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.26). For a sequence of instances of
Theorem 3.4 with `M_ℓ → ∞` and the same test, if `Λ_{F,ℓ} → Λ_∞`, `η_ℓ ≤ η_∞` for all sufficiently
large `ℓ`, `(2 + Φ_{max,ℓ})δ_{G,ℓ} → 0`, and `ε ≥ 0` is a constant with `2ε < |Λ_∞| − η_∞`, then there
are `c > 0` and `ℓ₀` such that, for every `ℓ ≥ ℓ₀`, every classical algorithm that samples within `ε`
on `G_ℓ` makes more than `cM_ℓ/log(2K_ℓ)` queries on some input in `G_ℓ`, and more than that many in
expectation on some input in `G_ℓ`.

**Formalization Note** `c` and `ℓ₀` come before the algorithm. An instance is `TransferInstance`; its
numbers `q`, `τ` are chosen in the proof by Lemma 3.3. -/
theorem corollary_3_6 (k : TestKind) (I : ℕ → TransferInstance k)
    (hM : Filter.Tendsto (fun ℓ => bigM (I ℓ).m) Filter.atTop Filter.atTop)
    (Λinf ηinf : ℝ)
    (hΛ : Filter.Tendsto (fun ℓ => Lambda k (I ℓ).S (I ℓ).γ (I ℓ).β (I ℓ).d) Filter.atTop
      (nhds Λinf))
    (hη : ∀ᶠ ℓ in Filter.atTop, (I ℓ).η ≤ ηinf)
    (hδ : Filter.Tendsto (fun ℓ => (2 + PhiMax (I ℓ).S (I ℓ).γ (I ℓ).β (I ℓ).d) *
        uProb (fun f : Qubits (I ℓ).m → ℤˣ => f ∉ (I ℓ).G)) Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 ≤ ε) (hgap : 2 * ε < |Λinf| - ηinf) :
    ∃ c : ℝ, 0 < c ∧ ∃ ℓ₀ : ℕ, ∀ ℓ, ℓ₀ ≤ ℓ →
      letI := (I ℓ).instY
      ∀ A : QueryAlg (Qubits (I ℓ).m) ℤˣ (I ℓ).Y,
        (∀ f ∈ (I ℓ).G, A.sampleErr (directRespond f) (lenSqDist ((I ℓ).x f)) ≤ ε) →
        (∃ f ∈ (I ℓ).G, ¬ A.MakesAtMostReal (directRespond f)
          (c * bigM (I ℓ).m / Real.log (2 * (I ℓ).S.card))) ∧
        (∃ f ∈ (I ℓ).G, ENNReal.ofReal (c * bigM (I ℓ).m / Real.log (2 * (I ℓ).S.card)) <
          A.expQueries (directRespond f)) := by sorry

end QuarticGap
