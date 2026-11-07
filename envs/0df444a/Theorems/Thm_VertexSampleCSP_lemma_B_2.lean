-- Prove2me | Theorems.Thm_VertexSampleCSP_lemma_B_2
-- name    : VertexSampleCSP.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:31.193391+00:00
-- url     : https://prove2.me/theorems/7f34ef6f-aea7-4041-b149-f488e5d7d5bb
-- title:
--   Lemma B.2, p.15 — weighted telescoping: $|P(x)-P(y)|\le\sigma_r(\rho)\sqrt\tau N^{(r-2)/2}\|B(x-y)\|$
-- statement:
--   Fix an instance on $V$ with $N=|V|$ and positive weights on the relevant variables, with $W,B,\tau$ as in Appendix B.
--
--   1. For all vectors $z,w_2,\dots,w_r$:
--
--   $$T[z,w_2,\dots,w_r]=\langle Bz,\ W^{1/2}w_2\otimes w_3\otimes\dots\otimes w_r\rangle.$$
--
--   2. If $x\in\Delta$ and $y\in\rho^{-1}\Delta_S$ for some $S\subseteq V$ and $0<\rho\le1$, then
--
--   $$|P(x)-P(y)|\le\sigma_r(\rho)\sqrt\tau\,N^{(r-2)/2}\,\|B(x-y)\|.$$
--
--   The second clause says that two points have nearby values of $P$ whenever their images under $B$ are close, even if the points themselves are far apart.
--
--   **Formalization Note** The vectors $w_2,\dots,w_r$ are a tuple indexed by `Fin (r - 1)`, tensors of order $r-1$ are functions on index tuples, and $N^{(r-2)/2}$ is a real power.
--
--   Differences from the source:
--
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: positive weights t_i for the relevant variables → t : V → ℝ with 0 < t i whenever γ_i > 0; reason: values on irrelevant variables are never read
--   - encoding: (ℝ^{V×[q]})^{⊗(r−1)} with its tensor norm → EuclideanSpace ℝ (Fin (r − 1) → V × Fin q); reason: the Hilbert–Schmidt norm is the Euclidean norm on index tuples
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma B.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_Instance_Gamma
import Definitions.Def_VertexSampleCSP_DeltaS
import Definitions.Def_VertexSampleCSP_tensorEntry
import Definitions.Def_VertexSampleCSP_flatten
import Definitions.Def_VertexSampleCSP_weightedFlatten
import Definitions.Def_VertexSampleCSP_sigmaR
open scoped Pointwise InnerProductSpace

namespace VertexSampleCSP

/-- **Lemma B.2 (Weighted telescoping).** Chang, *Optimal Vertex Sampling for Constraint
Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma B.2, p.15 (PDF
p.17): "For all vectors z, w2, . . . , wr, T[z, w2, . . . , wr] = ⟨Bz, W^{1/2}w2 ⊗ w3 ⊗ · · · ⊗ wr⟩.
Consequently, if x ∈ ∆ and y ∈ ρ^{−1}∆S for some S ⊆ V and 0 < ρ ≤ 1, then
|P(x) − P(y)| ≤ σr(ρ) √τ N^{(r−2)/2} ∥B(x − y)∥."

Fix positive weights `t_i` on the relevant variables (`γ_i(I) > 0`), with `W`, `B` and `τ` as in
Appendix B, and `N = |V|`.
1. For all `z, w_2, …, w_r ∈ ℝ^{V×[q]}`: `T[z, w_2, …, w_r] = ⟨Bz, W^{1/2}w_2 ⊗ w_3 ⊗ ⋯ ⊗ w_r⟩`.
2. For `S ⊆ V`, `0 < ρ ≤ 1`, `x ∈ Δ` and `y ∈ ρ⁻¹Δ_S`:
   `|P(x) − P(y)| ≤ σ_r(ρ) √τ N^{(r−2)/2} ‖B(x − y)‖`.

**Formalization Note.** The vectors `w_2, …, w_r` are a tuple `w : Fin (r − 1) → ℝ^{V×[q]}` with
`w_2 = w 0`; `T[z, w_2, …, w_r]` is `tensorMul I (consIdx z w)`. The vector
`W^{1/2}w_2 ⊗ w_3 ⊗ ⋯ ⊗ w_r` is `tensorVec` of `w` with its first entry replaced by `W^{1/2} w_2`.
Tensors of order `r − 1` are functions on index tuples with the Hilbert–Schmidt norm. `N^{(r−2)/2}`
is a real power. -/
theorem lemma_B_2 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r) (hq : 0 < q)
    (I : Instance V r q) (t : V → ℝ) (ht : ∀ i, 0 < I.gamma i → 0 < t i) :
    (∀ (z : EuclideanSpace ℝ (V × Fin q)) (w : Fin (r - 1) → EuclideanSpace ℝ (V × Fin q)),
      tensorMul I (consIdx z w) =
        ⟪weightedFlatten I t z,
          tensorVec (Function.update w ⟨0, by omega⟩ (wSqrtVec I t (w ⟨0, by omega⟩)))⟫_ℝ) ∧
    (∀ (S : Finset V) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∀ x ∈ DeltaS V q Finset.univ, ∀ y ∈ ρ⁻¹ • DeltaS V q S,
        |poly I x - poly I y| ≤
          sigmaR r ρ * Real.sqrt (tauW I t) * (Fintype.card V : ℝ) ^ (((r : ℝ) - 2) / 2) *
            ‖weightedFlatten I t (x - y)‖) := by sorry

end VertexSampleCSP
