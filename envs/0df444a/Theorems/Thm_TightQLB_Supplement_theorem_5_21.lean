-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_5_21
-- name    : TightQLB.Supplement.theorem_5_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:21:16.406943+00:00
-- url     : https://prove2.me/theorems/d8d074a9-7f7a-4928-bc29-5b56610fc7b2
-- title:
--   Theorem 5.21 — one-query growth: $\lambda(O_\phi F)\le\lambda(F)+54\sqrt{(d+1)/N}\,\|F\|$, also for the controlled query
-- statement:
--   Let $N=2^n$ with $n\ge1$, let $V$ be a space containing the query register $Q=\mathbb C|\bot\rangle\oplus\mathbb C^N$, and let the canonical oracle act as $O_\phi\otimes I$ pointwise in $\phi$. For every $d$ and every $F\in P_{\le d}(V)$,
--
--   $$
--   \lambda(O_\phi F)\le\lambda(F)+c_0\sqrt{\frac{d+1}{N}}\,\|F\|,\qquad c_0=54,
--   $$
--
--   and the same holds for the controlled query $O^c_\phi=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes O_\phi$. Here $\lambda$ is the progress measure and $\|F\|^2=\mathbb E_\phi\|F(\phi)\|^2$.
--
--   The paper states the theorem with "an absolute constant $c_0$" and its proof gives $c_0=54$. This is the growth half of Theorem 5.6: each query raises the progress measure by $O(\sqrt{(d+1)/N})$.
--
--   **Formalization Note** For the plain query $V=Q\times W$; for the controlled query $V=(C\times Q)\times W$ and the operator is the base mission's `queryOn`. $W$ is an arbitrary finite type.
--
--   Differences from the source:
--   - generalization: "There is an absolute constant c0" → c0 = 54; reason: the proof gives c0 = 54 (p. 44, PDF p. 47), and the explicit value implies the existential statement
--   - encoding: a space V containing Q, "V = W ⊗ Q after reordering" → Q × W for the plain query and (C × Q) × W for the controlled one, W any finite type; reason: same spaces up to reordering
--   - encoding: F ∈ P_{≤d}(V), a polynomial of degree at most d in α, ᾱ, unit vector in L²(Haar) → IsPoly d F (a polynomial representative on unit vectors) and E_ϕ‖F(ϕ)‖² = 1, V the coordinate space of a finite type; reason: same objects
--   - encoding: λ(F) = (Σ_k k‖P_k F‖²)^{1/2} with P_k the projection onto the level-k blocks → progress F, with ‖P_k F‖ the supremum of |⟨G, F⟩| over unit-ball elements G of the span of the level-k blocks and a tsum over k; reason: this is the norm of the orthogonal projection onto the closed span, and the blocks are pairwise orthogonal, so it agrees with the projection inside P_{≤d}(V)
--   - encoding: Dir(a), density ∝ Π p_i^{a_i−1} with respect to the uniform measure on the simplex → weight Π p_i^{a_i−1} against the (N−1)-dimensional Hausdorff measure restricted to the simplex, divided by its total weight; reason: the normalization of the uniform measure cancels
--   - encoding: a Haar-random unit vector of C^N → the published haarTargetLaw (the standard Gaussian on C^N normalized); reason: the same law on unit vectors
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 5.21, p. 43 (PDF p. 46); c0 = 54, p. 44 (PDF p. 47)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Level
open QAlgorithms

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 5.21 (One-query growth)**, p.43 (PDF p.46), with the constant of its proof.

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"There is an absolute constant `c₀` such that for all `F ∈ P_{≤d}(V)`,
`λ(O_ϕ F) ≤ λ(F) + c₀ √((d + 1)/N) ‖F‖`, and the same holds for the controlled query `O^c_ϕ`."
"The proof gives `c₀ = 54`" (p.44, PDF p.47).

**Formalization Note.**
* Stated with `c₀ = 54`, which implies the existential form.
* Plain query: `V = Q ⊗ W` with `Q = C|⊥⟩ ⊕ C^N` (`Option (Qubits n)`) and an arbitrary finite `W`
  ("Let `W` be the space of all registers other than the query register `Q`, so that `V = W ⊗ Q`
  after reordering", p.41); `O_ϕ` acts as `O_ϕ ⊗ I_W` pointwise in `ϕ`.
* Controlled query: `V = (C × Q) × W`, and `O^c_ϕ` is the published `TightQLB.queryOn (O_ϕ) W`.
* `λ` is `progress`, `‖F‖ = (E_ϕ‖F(ϕ)‖²)^{1/2}` is `hnorm`; `n ≥ 1` (§3.1). -/
theorem theorem_5_21 {n : ℕ} (hn : 1 ≤ n) {W : Type} [Fintype W] [DecidableEq W] (d : ℕ) :
    (∀ F : Fn n (Option (Qubits n) × W), IsPoly d F →
      progress (pointwise (fun ϕ => Matrix.kronecker (canonOracle ϕ) (1 : Matrix W W ℂ)) F) ≤
        progress F + c0 * Real.sqrt (((d : ℝ) + 1) / (2 : ℝ) ^ n) * hnorm F) ∧
    ∀ F : Fn n (Reg (Option (Qubits n)) W), IsPoly d F →
      progress (pointwise (fun ϕ => queryOn (canonOracle ϕ) W) F) ≤
        progress F + c0 * Real.sqrt (((d : ℝ) + 1) / (2 : ℝ) ^ n) * hnorm F := by sorry

end TightQLB.Supplement
