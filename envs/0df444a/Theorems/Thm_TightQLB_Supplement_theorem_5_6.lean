-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_5_6
-- name    : TightQLB.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:25:06.851856+00:00
-- url     : https://prove2.me/theorems/7db65a03-b05c-479f-9a8a-01204b7b3a96
-- title:
--   Theorem 5.6 — Haar lower bound for the canonical oracle: $\lambda(\Psi)\le\Lambda_{s,q}$ and $B(\mathcal A)\le\beta_N+2\sqrt2\Lambda_{s,q}+72\Lambda_{s,q}^2$
-- statement:
--   Let $N=2^n$ with $n\ge1$, and let the oracle be a Haar-random unit vector $|\phi\rangle=\sum_x\alpha_x|x\rangle\in\mathbb C^N$, accessed through the canonical oracle $O_\phi$. Consider an algorithm that receives $s$ copies of $|\phi\rangle$ in its registers before its first query and makes at most $q$ (possibly controlled) queries to $O_\phi$. Put $\beta_N=2N/(N+1)$, $c_0=54$ and
--
--   $$
--   \Lambda_{s,q}=\sqrt{\frac{s(s-1)}{N+s-1}}+\frac{c_0}{\sqrt N}\sum_{t=0}^{q-1}\sqrt{s+2t+1}.
--   $$
--
--   Then:
--
--   1. the final state $\Psi(\phi)=(V_\phi\otimes I_E)(|\phi\rangle^{\otimes s}\otimes\psi_0)$ of every such algorithm in normal form has progress measure $\lambda(\Psi)\le\Lambda_{s,q}$;
--   2. the expected score of every such experiment satisfies
--   $$
--   B(\mathcal A)\le\beta_N+2\sqrt2\,\Lambda_{s,q}+72\,\Lambda_{s,q}^2 .
--   $$
--
--   With no copies, $\Lambda_{0,q}=O(q^{3/2}/\sqrt N)$, so exceeding the ideal score $\beta_N$ by a constant requires $\Omega(N^{1/3})$ queries; with no queries it requires $\Omega(\sqrt N)$ copies.
--
--   **Formalization Note** The first clause quantifies over every oracle-independent unit vector $\psi_0$ and unitaries $U_0,\dots,U_q$; the second over every experiment with copies in channel form. The workspace and Eve's register are arbitrary finite types.
--
--   Differences from the source:
--   - reading: the operational experiment of Definition 3.1 (record, adaptive operations, at most q queries along every path) → a density matrix on A × E, q + 1 oracle-independent CPTP rounds on A, q controlled queries between them and a POVM, as in the base mission's TightQLB.Experiment; reason: the proof of Lemma 3.2, Steps 1–2, puts every experiment in this form and conversely every such channel form is an experiment of Definition 3.1
--   - reading: Ψ, "the final state" of the algorithm (§5, p. 30) → the final state (V_ϕ ⊗ I_E)(|ϕ⟩^{⊗s} ⊗ ψ₀) of every CopyNormalForm: an oracle-independent unit ψ₀ and unitaries U_0, …, U_q with controlled canonical queries between them; reason: §5 defines Ψ through the normal form of Lemma 3.2 with the copies prepended
--   - generalization: the theorems about the score alone, "the special case in which Eve's register is trivial" (p. 15) → every finite Eve register E and every joint initial state; reason: E = Unit is the source's statement; nothing acts on E, so the score does not depend on it
--   - encoding: the absolute constant c0 of Theorem 5.21 in Λ_{s,q} → c0 = 54; reason: "The proof gives c0 = 54" (p. 44, PDF p. 47)
--   - encoding: a Haar-random unit vector of C^N → the published haarTargetLaw (the standard Gaussian on C^N normalized); reason: the same law on unit vectors
--   - encoding: λ(F) = (Σ_k k‖P_k F‖²)^{1/2} with P_k the projection onto the level-k blocks → progress F, with ‖P_k F‖ the supremum of |⟨G, F⟩| over unit-ball elements G of the span of the level-k blocks and a tsum over k; reason: this is the norm of the orthogonal projection onto the closed span, and the blocks are pairwise orthogonal, so it agrees with the projection inside P_{≤d}(V)
--   - encoding: Dir(a), density ∝ Π p_i^{a_i−1} with respect to the uniform measure on the simplex → weight Π p_i^{a_i−1} against the (N−1)-dimensional Hausdorff measure restricted to the simplex, divided by its total weight; reason: the normalization of the uniform measure cancels
--   - encoding: N = 2^n, N^{1/3}, N^{−1/3}, √N → (2 : ℝ)^n with Real.rpow and Real.sqrt; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 5.6, p. 34 (PDF p. 37); c0 = 54, p. 44 (PDF p. 47)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Level
open QAlgorithms

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 5.6 (Haar lower bound for the canonical oracle)**, p.34 (PDF p.37).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let an algorithm receive `s` copies of `|ϕ⟩` and make at most `q` queries to `O_ϕ`. Then
`λ(Ψ) ≤ Λ_{s,q}` and `B(A) ≤ β_N + 2√2 Λ_{s,q} + 72 Λ_{s,q}²`, where
`Λ_{s,q} = √(s(s − 1)/(N + s − 1)) + (c₀/√N) Σ_{t=0}^{q−1} √(s + 2t + 1)`."

**Formalization Note.**
* `c₀ = 54` ("The proof gives `c₀ = 54`", p.44, PDF p.47); `Λ_{s,q}` is `Lam n s q`.
* The first clause is about the final state `Ψ(ϕ) = (V_ϕ ⊗ I_E)(|ϕ⟩^{⊗s} ⊗ ψ₀)` of the normal form
  of Lemma 3.2 with supplied copies (`CopyNormalForm`), for every oracle-independent `ψ₀` and
  unitaries; `λ` is the progress measure of Definition 5.3 (`progress`).
* The second clause is about every experiment of Definition 3.1 with the canonical oracle and `s`
  supplied copies, in channel form (`CopyExperiment`); `B(A)` is its expected score (12).
* Eve's register `E` and the workspace `W` are arbitrary finite types; `n ≥ 1` (§3.1). -/
theorem theorem_5_6 {n q s : ℕ} (hn : 1 ≤ n) {W E : Type} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E] :
    (∀ B : CopyNormalForm n q s W E, progress (ofVec B.finalState) ≤ Lam n s q) ∧
    ∀ A : CopyExperiment n q s W E,
      A.score ≤ betaN n + 2 * Real.sqrt 2 * Lam n s q + 72 * Lam n s q ^ 2 := by sorry

end TightQLB.Supplement
