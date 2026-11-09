-- Prove2me | Theorems.Thm_PerturbedWF_lemma_B_1
-- name    : PerturbedWF.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:42:06.883887+00:00
-- url     : https://prove2.me/theorems/784d1489-f469-42aa-be67-4ec1ed018e1c
-- title:
--   Lemma B.1: flow-model functions (B.1) satisfy the exchange property (simplex with convex costs; integral configurations with linear costs)
-- statement:
--   Let $G=(V,A)$ be a finite directed acyclic graph with bounds $\ell_a,u_a\in\mathbb R_{\ge0}\cup\{\infty\}$, a demand $b$ with $\sum_vb_v=0$, lower semicontinuous arc costs $\phi_a:\mathbb R_{\ge0}\to\mathbb R$, and a sink $s$ of in-degree $n$ and out-degree $0$ whose incoming arcs $a_i=(v_i,s)$ have zero cost; let $W$ be the function (B.1). Then:
--   1. if $\mathcal C=\{x\in[0,1]^n:\sum_ix_i=1\}$ and the arc costs $\phi_a$ are convex, $W$ satisfies the exchange property;
--   2. if $\mathcal C=\{x\in\mathbb Z^n_{\ge0}:\sum_ix_i=k\}$, the arc bounds $\ell,u$ and the demand $b$ are integral, and the arc costs $\phi_a$ are linear, $W$ satisfies the exchange property (with $\varepsilon=1$).
--
--   This is the source of the exchange property for every work function in the paper.
--
--   **Formalization Note.** The network is a `FlowNetwork`. In part 2 an integral bound is a natural number or $\infty$, an integral demand an integer, and a linear cost $\phi_a(z)=c_az$.
--
--   Differences from the source:
--   - reading: in part 2, 'the arc bounds ℓ, u ∈ ℝ^A_{≥0} … are integral' → each lower bound a natural number, each upper bound a natural number or ∞; reason: the setting of p.32 allows u_a = ∞ and every model of Appendix B uses u_a = ∞ by default ('Unless explicitly stated otherwise … u_a = ∞', p.33), so 'integral' is read as integral or infinite
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma B.1 and the setting before it, p.32 (PDF p.33)

import Mathlib
import Definitions.Def_PerturbedWF_WClass
import Definitions.Def_PerturbedWF_FlowNetwork

namespace PerturbedWF

/-- **Lemma B.1** (p.32, PDF p.33), in the setting of the paragraphs before it. C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

Let `G = (V, A)` be a finite DAG with bounds, demands and lower semicontinuous arc costs, with a
sink whose incoming zero-cost arcs `a_i` correspond to the points `i ∈ [n]`, and let `W` be the
function (B.1).
1. If `C = {x ∈ [0, 1]ⁿ : ∑ x_i = 1}` and the arc costs `φ_a : ℝ_{≥0} → ℝ` are convex, then `W`
   satisfies the exchange property.
2. If `C = {x ∈ ℤⁿ_{≥0} : ∑ x_i = k}`, the arc bounds `ℓ, u` and the demand `b` are integral, and
   the arc costs `φ_a` are linear, then `W` satisfies the exchange property.

**Formalization Note.** The network is a `FlowNetwork` (acyclicity as a rank function). In part 2
an integral bound is a natural number or `∞` (the paper's models use `u_a = ∞`), an integral
demand is an integer, and a linear cost is `φ_a(z) = c_a z`. For an integral `C` the exchange
property requires `ε = 1` (Definition 2.1). -/
theorem lemma_B_1 {ι Node Arc : Type} [Fintype ι] [DecidableEq ι] [Fintype Node]
    [DecidableEq Node] [Fintype Arc] (N : FlowNetwork ι Node Arc) :
    ((∀ a, ConvexOn ℝ (Set.Ici 0) (N.cost a)) → ExchangeProperty (simplex ι) N.flowW) ∧
      ∀ k : ℕ, (∀ a, ∃ z : ℕ, N.lower a = z) → (∀ a, N.upper a = ⊤ ∨ ∃ z : ℕ, N.upper a = z) →
        (∀ v, ∃ z : ℤ, N.demand v = z) → (∃ c : Arc → ℝ, ∀ a s, N.cost a s = c a * s) →
        ExchangeProperty (kConfig ι k) N.flowW := by sorry

end PerturbedWF
