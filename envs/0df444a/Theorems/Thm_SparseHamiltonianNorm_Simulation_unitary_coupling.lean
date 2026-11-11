-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_unitary_coupling
-- name    : SparseHamiltonianNorm.Simulation.unitary_coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:03.264192+00:00
-- url     : https://prove2.me/theorems/1dc5a5a1-8431-4866-9ac2-8189ceba9c91
-- title:
--   Lemma 8 — Unitary coupling independent of queried entries
-- statement:
--   Let $d\ge1$, $\Lambda>0$, $t\ge0$, and let $V:\mathbb C^n\to\mathbb C^e$ satisfy $V^\dagger V=I$. The Volterra map $W_t$ from Eqs. (34)–(35) is a complex-linear bijection preserving the orthogonal-sum inner product on $\mathbb C^n\oplus L^2([0,t];\mathbb C^e)$. Its output fields are square integrable.
--
--   This is the source's unitary coupling. Its definition takes only $d,\Lambda,t,V$ and has no queried matrix argument, so the asserted interaction is independent of the hidden entries, including at $t=0$.
--
--   Differences from the source:
--   - generalization: the public sparse-lift isometry in Section 3 → any isometry between finite complex Euclidean spaces; reason: the coupling depends only on isometry and the public scalars, and every source embedding is included
--   - encoding: unitary operator on the Hilbert direct sum → a complex-linear bijection preserving the sum inner product, with explicit square-integrability of its output field; reason: this spells out unitarity and the well-defined L2 quotient operation rather than imposing them on a definition
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Lemma 8, p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=14; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Coupling

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
/-- Li--Wang, Lemma 8, p.14. Independence from queried entries is enforced by the definition's arguments. -/
theorem unitary_coupling (n e d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (hd : 1 ≤ d) (hΛ : 0 < Λ) (ht : 0 ≤ t) (hV : V.conjTranspose * V = 1) :
    IsSumUnitary (coupling d Λ t V) ∧
    ∀ (ξ : Vec n) (q : History e t),
      MeasureTheory.MemLp (outputField d Λ V ξ q) 2 (historyMeasure t) := by sorry
end SparseHamiltonianNorm.Simulation
